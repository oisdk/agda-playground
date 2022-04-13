{-# OPTIONS --no-termination-check #-}

module Hyper.NonStrictPositive where

open import Prelude

_↬′_ : Type a → Type b → Type (a ℓ⊔ b)

{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive
  infixl 4 _·_
  field _·_ : (B ↬′ A) → B

A ↬′ B = (B ↬ A) → B

open _↬_ public

infixr 9 _⊙_ _⊙′_ _⊙″_
mutual
  _⊙″_ : B ↬′ C → A ↬ B → A ↬′ C
  (f ⊙″ g) k = f (g ⊙ k)

  _⊙′_ : B ↬ C → (A ↬′ B) → (A ↬′ C)
  (f ⊙′ g) k = f · g ⊙″ k

  _⊙_ : B ↬ C → A ↬ B → A ↬ C
  f ⊙ g · k = f · g ⊙′ k
