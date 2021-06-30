{-# OPTIONS --cubical --safe #-}

module Data.Bits.Order where

open import Data.Bits
open import Data.Bool
open import Level

infix 4 _≤ᴮ_ _<ᴮ_
_≤ᴮ_ _<ᴮ_ : Bits → Bits → Bool
[]    ≤ᴮ ys    = true
0∷ xs ≤ᴮ []    = false
0∷ xs ≤ᴮ 0∷ ys = xs ≤ᴮ ys
0∷ xs ≤ᴮ 1∷ ys = true
1∷ xs ≤ᴮ []    = false
1∷ xs ≤ᴮ 0∷ ys = false
1∷ xs ≤ᴮ 1∷ ys = xs ≤ᴮ ys

xs    <ᴮ []    = false
[]    <ᴮ 0∷ ys = true
0∷ xs <ᴮ 0∷ ys = xs <ᴮ ys
1∷ xs <ᴮ 0∷ ys = false
[]    <ᴮ 1∷ ys = true
0∷ xs <ᴮ 1∷ ys = true
1∷ xs <ᴮ 1∷ ys = xs <ᴮ ys

infix 4 _≤_ _<_
_≤_ _<_ : Bits → Bits → Type
xs ≤ ys = T (xs ≤ᴮ ys)
xs < ys = T (xs <ᴮ ys)
