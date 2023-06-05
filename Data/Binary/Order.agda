{-# OPTIONS --cubical --safe #-}

module Data.Binary.Order where

open import Prelude
open import Data.Binary.Definition

infix 4 _≲ᴮ_&_
_≲ᴮ_&_ : 𝔹 → 𝔹 → Bool → Bool
0ᵇ    ≲ᴮ ys    & true  = true
0ᵇ    ≲ᴮ 0ᵇ    & false = false
0ᵇ    ≲ᴮ 1ᵇ ys & false = true
0ᵇ    ≲ᴮ 2ᵇ ys & false = true
1ᵇ xs ≲ᴮ 0ᵇ    & s     = false
1ᵇ xs ≲ᴮ 1ᵇ ys & s     = xs ≲ᴮ ys & s
1ᵇ xs ≲ᴮ 2ᵇ ys & s     = xs ≲ᴮ ys & true
2ᵇ xs ≲ᴮ 0ᵇ    & s     = false
2ᵇ xs ≲ᴮ 1ᵇ ys & s     = xs ≲ᴮ ys & false
2ᵇ xs ≲ᴮ 2ᵇ ys & s     = xs ≲ᴮ ys & s

infix 4 _≤ᴮ_ _<ᴮ_
_≤ᴮ_ : 𝔹 → 𝔹 → Bool
xs ≤ᴮ ys = xs ≲ᴮ ys & true

_<ᴮ_ : 𝔹 → 𝔹 → Bool
xs <ᴮ ys = xs ≲ᴮ ys & false

infix 4 _≤_ _<_
_≤_ : 𝔹 → 𝔹 → Type
xs ≤ ys = T (xs ≤ᴮ ys)

_<_ : 𝔹 → 𝔹 → Type
xs < ys = T (xs <ᴮ ys)
