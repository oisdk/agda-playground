{-# OPTIONS --cubical --safe #-}

module Data.Bits.Equatable where

open import Data.Bits
open import Prelude

_≡ᴮ_ : Bits → Bits → Bool
[]      ≡ᴮ []      = true
(0∷ xs) ≡ᴮ (0∷ ys) = xs ≡ᴮ ys
(1∷ xs) ≡ᴮ (1∷ ys) = xs ≡ᴮ ys
_       ≡ᴮ _       = false

open import Relation.Nullary.Discrete.FromBoolean

module EqBits where
  sound : ∀ n m →  T (n ≡ᴮ m) → n ≡ m
  sound []     []     p = refl
  sound (0∷ n) (0∷ m) p = cong 0∷_ (sound n m p)
  sound (1∷ n) (1∷ m) p = cong 1∷_ (sound n m p)
  
  complete : ∀ n → T (n ≡ᴮ n)
  complete [] = tt
  complete (0∷ n) = complete n
  complete (1∷ n) = complete n

_≟_ : Discrete Bits
_≟_ = from-bool-eq record { EqBits }
