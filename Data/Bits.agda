{-# OPTIONS --cubical --safe #-}

module Data.Bits where

open import Prelude

infixr 5 0∷_ 1∷_
data Bits : Type₀ where
  [] : Bits
  0∷_ : Bits → Bits
  1∷_ : Bits → Bits

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

infix 4 _≲ᴮ_&_
_≲ᴮ_&_ : Bits → Bits → Bool → Bool
[]    ≲ᴮ ys    & true  = true
[]    ≲ᴮ []    & false = false
[]    ≲ᴮ 0∷ ys & false = true
[]    ≲ᴮ 1∷ ys & false = true
0∷ xs ≲ᴮ []    & s     = false
0∷ xs ≲ᴮ 0∷ ys & s     = xs ≲ᴮ ys & s
0∷ xs ≲ᴮ 1∷ ys & s     = xs ≲ᴮ ys & true
1∷ xs ≲ᴮ []    & s     = false
1∷ xs ≲ᴮ 0∷ ys & s     = xs ≲ᴮ ys & false
1∷ xs ≲ᴮ 1∷ ys & s     = xs ≲ᴮ ys & s

infix 4 _≤ᴮ_ _<ᴮ_
_≤ᴮ_ : Bits → Bits → Bool
xs ≤ᴮ ys = xs ≲ᴮ ys & true

_<ᴮ_ : Bits → Bits → Bool
xs <ᴮ ys = xs ≲ᴮ ys & false

infix 4 _≤_ _<_
_≤_ : Bits → Bits → Type₀
xs ≤ ys = T (xs ≤ᴮ ys)

_<_ : Bits → Bits → Type₀
xs < ys = T (xs <ᴮ ys)
