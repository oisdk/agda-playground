{-# OPTIONS --cubical --safe #-}

module Data.Binary.Subtraction where

open import Data.Binary.Definition
open import Data.Nat

double : 𝔹 → 𝔹
double 0ᵇ      = 0ᵇ
double (1ᵇ xs) = 2ᵇ double xs
double (2ᵇ xs) = 2ᵇ 1ᵇ xs

dec : 𝔹 → 𝔹
dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = double xs

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = ones n (1ᵇ xs)

fromZ₁ : ℕ → 𝔹 → 𝔹
fromZ₁ n 0ᵇ      = 0ᵇ
fromZ₁ n (1ᵇ xs) = 2ᵇ ones n (double xs)
fromZ₁ n (2ᵇ xs) = 2ᵇ ones (suc n) xs

mutual
  compl₁′ : ℕ → 𝔹 → 𝔹 → 𝔹
  compl₁′ n 0ᵇ      _       = 2ᵇ ones n 0ᵇ
  compl₁′ n (1ᵇ xs) 0ᵇ      = fromZ₁ (suc n) xs
  compl₁′ n (2ᵇ xs) 0ᵇ      = 2ᵇ ones n (double xs)
  compl₁′ n (1ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (compl₁′ 0 xs ys)
  compl₁′ n (1ᵇ xs) (2ᵇ ys) = compl₁′ (suc n) xs ys
  compl₁′ n (2ᵇ xs) (1ᵇ ys) = compl₂′ (suc n) xs ys
  compl₁′ n (2ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (compl₁′ 0 xs ys)

  compl₂′ : ℕ → 𝔹 → 𝔹 → 𝔹
  compl₂′ n xs      0ᵇ      = fromZ₁ n xs
  compl₂′ n 0ᵇ      _       = 0ᵇ
  compl₂′ n (1ᵇ xs) (1ᵇ ys) = compl₂′ (suc n) xs ys
  compl₂′ n (1ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (compl₁′ 0 xs ys)
  compl₂′ n (2ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (compl₂′ 0 xs ys)
  compl₂′ n (2ᵇ xs) (2ᵇ ys) = compl₂′ (suc n) xs ys

mutual
  compl₁ : 𝔹 → 𝔹 → 𝔹
  compl₁ xs      0ᵇ      = dec xs
  compl₁ 0ᵇ      _       = 1ᵇ 0ᵇ
  compl₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ compl₁ xs ys
  compl₁ (1ᵇ xs) (2ᵇ ys) = compl₁′ zero xs ys
  compl₁ (2ᵇ xs) (1ᵇ ys) = compl₂′ zero xs ys
  compl₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ compl₁ xs ys

  compl₂ : 𝔹 → 𝔹 → 𝔹
  compl₂ 0ᵇ      _       = 0ᵇ
  compl₂ xs      0ᵇ      = xs
  compl₂ (1ᵇ xs) (1ᵇ ys) = compl₂′ zero xs ys
  compl₂ (1ᵇ xs) (2ᵇ ys) = 1ᵇ compl₁ xs ys
  compl₂ (2ᵇ xs) (1ᵇ ys) = 1ᵇ compl₂ xs ys
  compl₂ (2ᵇ xs) (2ᵇ ys) = compl₂′ zero xs ys

open import Data.Binary.Order
open import Data.Bool

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = if n ≤ᴮ m then 0ᵇ else compl₂ n m

open import Data.Binary.Testers
open import Path using (refl)

_ : test _-_ _∸_ 30
_ = refl
