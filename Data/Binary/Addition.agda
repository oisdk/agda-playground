{-# OPTIONS --without-K --safe #-}

module Data.Binary.Addition where

open import Data.Binary.Definition
open import Data.Binary.Increment

add₁ : 𝔹 → 𝔹 → 𝔹
add₂ : 𝔹 → 𝔹 → 𝔹

add₁ 0ᵇ      ys      = inc ys
add₁ (1ᵇ xs) 0ᵇ      = 2ᵇ xs
add₁ (2ᵇ xs) 0ᵇ      = 1ᵇ inc xs
add₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ add₁ xs ys
add₁ (1ᵇ xs) (2ᵇ ys) = 2ᵇ add₁ xs ys
add₁ (2ᵇ xs) (1ᵇ ys) = 2ᵇ add₁ xs ys
add₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ add₂ xs ys

add₂ 0ᵇ      0ᵇ      = 2ᵇ 0ᵇ
add₂ 0ᵇ      (1ᵇ ys) = 1ᵇ inc ys
add₂ 0ᵇ      (2ᵇ ys) = 2ᵇ inc ys
add₂ (1ᵇ xs) 0ᵇ      = 1ᵇ inc xs
add₂ (2ᵇ xs) 0ᵇ      = 2ᵇ inc xs
add₂ (1ᵇ xs) (1ᵇ ys) = 2ᵇ add₁ xs ys
add₂ (1ᵇ xs) (2ᵇ ys) = 1ᵇ add₂ xs ys
add₂ (2ᵇ xs) (1ᵇ ys) = 1ᵇ add₂ xs ys
add₂ (2ᵇ xs) (2ᵇ ys) = 2ᵇ add₂ xs ys

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    + ys    = ys
1ᵇ xs + 0ᵇ    = 1ᵇ xs
2ᵇ xs + 0ᵇ    = 2ᵇ xs
1ᵇ xs + 1ᵇ ys = 2ᵇ (xs + ys)
1ᵇ xs + 2ᵇ ys = 1ᵇ add₁ xs ys
2ᵇ xs + 1ᵇ ys = 1ᵇ add₁ xs ys
2ᵇ xs + 2ᵇ ys = 2ᵇ add₁ xs ys
