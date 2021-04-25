{-# OPTIONS --cubical --safe #-}

module Data.Binary.Subtraction where

open import Data.Binary.Definition
open import Data.Nat

dec′ : 𝔹 → 𝔹
dec : 𝔹 → 𝔹

dec′ 0ᵇ = 0ᵇ
dec′ (1ᵇ xs) = 2ᵇ dec′ xs
dec′ (2ᵇ xs) = 2ᵇ 1ᵇ xs

dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = dec′ xs

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = ones n (1ᵇ xs)

fromZ₁ : ℕ → 𝔹 → 𝔹
fromZ₁ n 0ᵇ      = 0ᵇ
fromZ₁ n (1ᵇ xs) = fromZ₁ (suc n) xs
fromZ₁ n (2ᵇ xs) = 2ᵇ ones n (fromZ₁ 0 xs)

fromZ : 𝔹 → 𝔹
fromZ 0ᵇ = 0ᵇ
fromZ (1ᵇ xs) = fromZ₁ zero xs
fromZ (2ᵇ xs) = 1ᵇ fromZ xs

compl : 𝔹 → 𝔹
compl 0ᵇ = 1ᵇ 0ᵇ
compl (1ᵇ xs) = 2ᵇ compl xs
compl (2ᵇ xs) = 1ᵇ compl xs

extend : 𝔹 → 𝔹 → 𝔹
extend 0ᵇ      ys = ys
extend (1ᵇ xs) 0ᵇ = 2ᵇ extend xs 0ᵇ
extend (2ᵇ xs) 0ᵇ = 2ᵇ extend xs 0ᵇ
extend (1ᵇ xs) (1ᵇ ys) = 1ᵇ extend xs ys
extend (1ᵇ xs) (2ᵇ ys) = 2ᵇ extend xs ys
extend (2ᵇ xs) (1ᵇ ys) = 1ᵇ extend xs ys
extend (2ᵇ xs) (2ᵇ ys) = 2ᵇ extend xs ys

open import Data.Binary.Order
open import Data.Bool
open import Data.Binary.Addition


infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = if n ≤ᴮ m then 0ᵇ else fromZ (add₂ n (extend n (compl m)))
