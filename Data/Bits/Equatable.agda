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

sound-== : ∀ n m →  T (n ≡ᴮ m) → n ≡ m
sound-== [] [] p i = []
sound-== (0∷ n) (0∷ m) p i = 0∷ sound-== n m p i
sound-== (1∷ n) (1∷ m) p i = 1∷ sound-== n m p i

complete-== : ∀ n → T (n ≡ᴮ n)
complete-== [] = tt
complete-== (0∷ n) = complete-== n
complete-== (1∷ n) = complete-== n

_≟_ : Discrete Bits
_≟_ = from-bool-eq _≡ᴮ_ sound-== complete-==
