{-# OPTIONS --safe #-}

module Codata.Delay where

open import Prelude
open import Data.Nat.Properties
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

_⊑_ : Maybe A → Maybe A → Type _
nothing ⊑ _ = Poly.⊤
just x ⊑ nothing = Poly.⊥
just x ⊑ just y  = x ≡ y

record Delay (A : Type a) : Type a where
  field
    explore  : ℕ → Maybe A
    converge : ∀ n m → (n≤m : n ≤ m) → explore n ⊑ explore m

open Delay public

never : Delay A
never .explore _ = nothing
never .converge n m x = _

later : Delay A → Delay A
later xs .explore zero = nothing
later xs .explore (suc n) = xs .explore n
later xs .converge zero _ n≤m = _
later xs .converge (suc n) (suc m) n≤m = xs .converge n m n≤m

now : A → Delay A
now x .explore _ = just x
now x .converge n m n≤m = refl

bind : (A → Delay B) → Delay A → Delay B
bind k xs .explore n = maybe nothing (flip explore n ∘ k) (xs .explore n)
bind k xs .converge n m n≤m with xs .explore n | xs .explore m | xs .converge n m n≤m
bind k xs .converge n m n≤m | nothing | _ | _ = _
bind k xs .converge n m n≤m | just x | just y | x≡y = subst (λ e → _ ⊑ explore (k e) m) x≡y (k x .converge n m n≤m)

until′ : (A → A ⊎ B) → A ⊎ B → ℕ → Maybe B
until′ f (inr x) n = just x
until′ f (inl x) zero = nothing
until′ f (inl x) (suc n) = until′ f (f x) n

until-converge : (f : A → A ⊎ B) (x : A ⊎ B) → ∀ n m → n ≤ m → until′ f x n ⊑ until′ f x m
until-converge f (inr x) n m n≤m = refl
until-converge f (inl x) zero m n≤m = _
until-converge f (inl x) (suc n) (suc m) n≤m = until-converge f (f x) n m n≤m

until : (A → A ⊎ B) → A → Delay B
until f x .explore = until′ f (f x)
until f x .converge = until-converge f (f x)

record Delay′ (A : Type a) : Type a where
  coinductive
  field force : A ⊎ Delay′ A
open Delay′ public

coind′ : (ℕ → Maybe A) → Delay′ A
coind′ xs .force with xs zero
... | nothing = inr (coind′ (xs ∘ suc))
... | just x = inl x

coind : Delay A → Delay′ A
coind xs = coind′ (xs .explore)

ind′ : Delay′ A → ℕ → Maybe A
ind′ xs n with xs .force
ind′ xs n | inl x = just x
ind′ xs zero | inr x = nothing
ind′ xs (suc n) | inr x = ind′ x n

ind″ : (xs : Delay′ A) → ∀ n m → n ≤ m → ind′ xs n ⊑ ind′ xs m
ind″ xs n m n≤m with xs .force
ind″ xs n m n≤m | inl x = refl
ind″ xs zero m n≤m | inr x = _
ind″ xs (suc n) (suc m) n≤m | inr x = ind″ x n m n≤m

ind : Delay′ A → Delay A
ind xs .explore = ind′ xs
ind xs .converge = ind″ xs

-- Delay′⇔Delay : Delay′ A ⇔ Delay A
-- Delay′⇔Delay .fun = ind
-- Delay′⇔Delay .inv = coind
-- Delay′⇔Delay .rightInv = {!!}
-- Delay′⇔Delay .leftInv = {!!}
