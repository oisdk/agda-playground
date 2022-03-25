{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Free.Quotiented.Containers where

open import Prelude
open import Container
open import HITs.SetQuotients

-- data Syntax (F : Container ℓzero ℓzero) (A : Type) : Type where
--   return : A → Syntax  A
--   op : ⟦ F ⟧ (Syntax  A) → Syntax  A

-- Free : (F : Container ℓzero ℓzero) (_~_ : ∀ {X} → Syntax  X → Syntax  X → Type) (A : Type)  → Type
-- Free _~_ A = Syntax  A / _~_

-- private
--   variable
--     F G : Container ℓzero ℓzero
--     _~_ : ∀ {X} → Syntax  X → Syntax  X → Type

-- smap : (A → B) → Syntax  A → Syntax  B
-- smap f (return x) = return (f x)
-- smap f (op x) = op (cmap (smap f) x)

-- module _ {_~_ : ∀ {X} → Syntax  X → Syntax  X → Type} where
--   fmap : (A → B) → Free _~_ A → Free _~_ B
--   fmap f = rec squash/ ([_] ∘ smap f) {!!}

--   module _ {A : Type} where
--     join : Free _~_ (Free _~_ A) → Free _~_ A
--     join = rec squash/ ϕ {!!}
--       where
--         ϕ : Syntax  (Free _~_ A) → Free _~_ A
--         ϕ (return x) = x
--         ϕ (op x)     = {!!}

data Syntax (A : Type) : Type where
  return : A → Syntax A
  op : (Bool → Syntax A) → Syntax A

Free : (_~_ : ∀ {X} → Syntax  X → Syntax  X → Type) (A : Type)  → Type
Free _~_ A = Syntax  A / _~_

private
  variable
    _~_ : ∀ {X} → Syntax  X → Syntax  X → Type

smap : (A → B) → Syntax  A → Syntax  B
smap f (return x) = return (f x)
smap f (op x) = op (smap f ∘ x)

sjoin : Syntax (Syntax A) → Syntax A
sjoin (return xs) = xs
sjoin (op x) = op (sjoin ∘ x)

open import Data.Vec.Iterated


Traversal′ : (Type → Type) → Type → Type₁
Traversal′ A B = ∃ n × Vec B n × (∀ {C} → Vec C n → A C)

Traversal : (Type → Type) → Type → Type₁
Traversal A B = A B → Traversal′ A B

open import Data.Nat

holes : Traversal Syntax A
holes (return x) = 1 , (x ∷ []) , (λ {  (y ∷ []) → return y })
holes (op x) =
  let lhs = holes (x false)
      rhs = holes (x true)
  in (fst lhs + fst rhs) , (lhs .snd .fst ++ rhs .snd .fst) , op ∘ uncurry bool′ ∘ map-Σ (lhs .snd .snd) (rhs .snd .snd) ∘ split

-- -- lens      A B = A → (B × B → A)
-- -- traversal A B = A → ∃ n × Vec n B × (Vec n B → A)
--

open import HITs.SetQuotients.Prod

module _ {_~_ : ∀ {X} → Syntax  X → Syntax  X → Type} where
  fmap : (A → B) → Free _~_ A → Free _~_ B
  fmap f = rec squash/ ([_] ∘ smap f) {!!}

  module _ {A B : Type} where
    join : Free _~_ (Free _~_ A) → Free _~_ A
    join = rec squash/ (ϕ ∘ holes) {!!}
      where
        ϕ : Traversal′ Syntax (Free _~_ A) → Free _~_ A
        ϕ (n , xs , k) = rec squash/ ([_] ∘ sjoin ∘ k) {!!} (trav xs)
