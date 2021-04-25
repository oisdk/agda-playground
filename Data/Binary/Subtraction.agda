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

open import Data.Binary.Addition

mutual
  twos₁ : 𝔹 → 𝔹
  twos₁ 0ᵇ      = 1ᵇ 0ᵇ
  twos₁ (1ᵇ xs) = 2ᵇ twos₁ xs
  twos₁ (2ᵇ xs) = 1ᵇ twos₂ xs

  twos₂ : 𝔹 → 𝔹
  twos₂ 0ᵇ      = 2ᵇ 0ᵇ
  twos₂ (1ᵇ xs) = 1ᵇ twos₂ xs
  twos₂ (2ᵇ xs) = 2ᵇ twos₂ xs

mutual
  compl₁ : 𝔹 → 𝔹 → 𝔹
  compl₁ 0ᵇ      _       = 2ᵇ 0ᵇ
  compl₁ (1ᵇ xs) 0ᵇ      = 1ᵇ twos₁ xs
  compl₁ (2ᵇ xs) 0ᵇ      = 2ᵇ twos₁ xs
  compl₁ (1ᵇ xs) (1ᵇ ys) = 2ᵇ compl₁ xs ys
  compl₁ (1ᵇ xs) (2ᵇ ys) = 1ᵇ compl₁ xs ys
  compl₁ (2ᵇ xs) (1ᵇ ys) = 1ᵇ compl₂ xs ys
  compl₁ (2ᵇ xs) (2ᵇ ys) = 2ᵇ compl₁ xs ys

  compl₂ : 𝔹 → 𝔹 → 𝔹
  compl₂ 0ᵇ      _       = 1ᵇ 1ᵇ 0ᵇ
  compl₂ (1ᵇ xs) 0ᵇ      = 2ᵇ twos₁ xs
  compl₂ (2ᵇ xs) 0ᵇ      = 1ᵇ twos₂ xs
  compl₂ (1ᵇ xs) (1ᵇ ys) = 1ᵇ compl₂ xs ys
  compl₂ (1ᵇ xs) (2ᵇ ys) = 2ᵇ compl₁ xs ys
  compl₂ (2ᵇ xs) (1ᵇ ys) = 2ᵇ compl₂ xs ys
  compl₂ (2ᵇ xs) (2ᵇ ys) = 1ᵇ compl₂ xs ys

open import Data.Binary.Order
open import Data.Bool

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = if n ≤ᴮ m then 0ᵇ else fromZ (compl₂ n m)

open import Data.Binary.Testers
open import Path using (refl)

_ : test _-_ _∸_ 30
_ = refl
