{-# OPTIONS --cubical --safe #-}

module Data.Bits.Order.Reverse where

open import Prelude
open import Data.Bits

-- Least significant bit first

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
