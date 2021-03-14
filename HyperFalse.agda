{-# OPTIONS --cubical #-}

module HyperFalse where

open import Prelude hiding (false)


{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive; constructor hyp
  field invoke : (B ↬ A) → B
open _↬_

yes? : ⊥ ↬ ⊥
yes? .invoke h = h .invoke h

no! : (⊥ ↬ ⊥) → ⊥
no! h = h .invoke h

boom : ⊥
boom = no! yes?
