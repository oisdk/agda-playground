{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Weighted.Definition {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels

infixr 5 _&_∷_
data W (A : Type a) : Set (a ℓ⊔ ℓ) where
  []     : W A
  _&_∷_  : (p : 𝑅) → (x : A) → W A → W A

  dup : ∀ p q x xs → p & x ∷ q & x ∷ xs ≡ p + q & x ∷ xs
  com : ∀ p x q y xs → p & x ∷ q & y ∷ xs ≡ q & y ∷ p & x ∷ xs
  del : ∀ x xs → 0# & x ∷ xs ≡ xs

  trunc : isSet (W A)
