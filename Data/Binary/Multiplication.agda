{-# OPTIONS --cubical --safe #-}

module Data.Binary.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Addition

double : 𝔹 → 𝔹
double 0ᵇ = 0ᵇ
double (1ᵇ xs) = 2ᵇ double xs
double (2ᵇ xs) = 2ᵇ 1ᵇ xs

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    * ys = 0ᵇ
1ᵇ xs * ys = ys + double (ys * xs)
2ᵇ xs * ys = double (ys + ys * xs)
