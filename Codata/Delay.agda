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
    explore   : ℕ → Maybe A
    converges : ∀ n m → (n≤m : n ≤ m) → explore n ⊑ explore m

open Delay public

never : Delay A
never .explore _ = nothing
never .converges n m x = _

later : Delay A → Delay A
later xs .explore zero = nothing
later xs .explore (suc n) = xs .explore n
later xs .converges zero _ n≤m = _
later xs .converges (suc n) (suc m) n≤m = xs .converges n m n≤m

now : A → Delay A
now x .explore _ = just x
now x .converges n m n≤m = refl

bind : (A → Delay B) → Delay A → Delay B
bind k xs .explore n = maybe nothing (flip explore n ∘ k) (xs .explore n)
bind k xs .converges n m n≤m with xs .explore n | xs .explore m | xs .converges n m n≤m
bind k xs .converges n m n≤m | nothing | _ | _ = _
bind k xs .converges n m n≤m | just x | just y | x≡y = subst (λ e → _ ⊑ explore (k e) m) x≡y (k x .converges n m n≤m)

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
until f x .converges = until-converge f (f x)
