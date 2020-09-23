{-# OPTIONS --cubical --safe #-}

module Data.Array where

open import Data.Binary
open import Prelude

private
  variable
    ns : 𝔹

infixr 5 _∷₁_ _∷₂_ _∷_

data Array {a} (A : Type a) : 𝔹 → Type a where
  [] : Array A 0ᵇ
  _∷₁_ : A → Array (A × A) ns → Array A (1ᵇ ns)
  _∷₂_ : A × A → Array (A × A) ns → Array A (2ᵇ ns)

_∷_ : A → Array A ns → Array A (inc ns)
x  ∷ [] = x ∷₁ []
x₁ ∷ x₂ ∷₁ xs = (x₁ , x₂) ∷₂ xs
x₁ ∷ x₂ ∷₂ xs = x₁ ∷₁ x₂ ∷ xs
