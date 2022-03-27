{-# OPTIONS --cubical --guardedness #-}

module HyperFalse where

open import Prelude hiding (false)


{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  coinductive; constructor ⟪_⟫
  field invoke : (B ↬ A) → B
open _↬_

yes? : ⊥ ↬ ⊥
yes? = ⟪ (λ h →  h .invoke h) ⟫

no! : (⊥ ↬ ⊥) → ⊥
no! h = h .invoke h

boom : ⊥
boom = no! yes?

open import Data.List

record Tree (A : Type a) : Type a where
  inductive; pattern; constructor _&_
  field
    root : A
    children : List (Tree A)
open Tree

{-# NON_TERMINATING #-}
loop : A ↬ A
loop = ⟪ (λ k → k .invoke loop) ⟫

open import Data.Bool

{-# TERMINATING #-}
bfe : Tree A → List A
bfe t = f t d .invoke loop zero
  where
  f : Tree A → ((ℕ → List A) ↬ (ℕ → List A)) → ((ℕ → List A) ↬ (ℕ → List A))
  f (x & xs) fw .invoke bw n = x ∷ fw .invoke ⟪ bw .invoke ∘ flip (foldr f) xs ⟫ (suc n)

  d : ((ℕ → List A) ↬ (ℕ → List A))
  d .invoke k zero    = []
  d .invoke k (suc n) = k .invoke d n 
