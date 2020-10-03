{-# OPTIONS --cubical --safe #-}

module WellFounded where

open import Level

data Acc {a r} {A : Type a} (R : A → A → Type r) (x : A) : Type (a ℓ⊔ r) where
  acc : (∀ y → R y x → Acc R y) → Acc R x

WellFounded : ∀ {r} → (A → A → Type r) → Type _
WellFounded R = ∀ x → Acc R x
