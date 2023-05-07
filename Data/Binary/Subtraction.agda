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

_×2^suc_ : 𝔹 → ℕ → 𝔹
0ᵇ      ×2^suc n = 0ᵇ
(1ᵇ xs) ×2^suc n = 2ᵇ ones n (double xs)
(2ᵇ xs) ×2^suc n = 2ᵇ ones (suc n) xs

mutual
  -- sub₁ x y = (x - (y + 1)) × 2ⁿ
  sub₁ : ℕ → 𝔹 → 𝔹 → 𝔹
  sub₁ zero xs      0ᵇ      = dec xs
  sub₁ zero 0ᵇ      _       = 1ᵇ 0ᵇ
  sub₁ zero (1ᵇ xs) (1ᵇ ys) = 1ᵇ sub₁ 0 xs ys
  sub₁ zero (1ᵇ xs) (2ᵇ ys) = sub₁ 1 xs ys
  sub₁ zero (2ᵇ xs) (1ᵇ ys) = sub  1 xs ys
  sub₁ zero (2ᵇ xs) (2ᵇ ys) = 1ᵇ sub₁ 0 xs ys
  sub₁ (suc n) 0ᵇ      _       = 2ᵇ ones n 0ᵇ
  sub₁ (suc n) (1ᵇ xs) 0ᵇ      = xs ×2^suc suc n
  sub₁ (suc n) (2ᵇ xs) 0ᵇ      = 2ᵇ ones n (double xs)
  sub₁ (suc n) (1ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (sub₁ 1 xs ys)
  sub₁ (suc n) (1ᵇ xs) (2ᵇ ys) = sub₁ (suc (suc n)) xs ys
  sub₁ (suc n) (2ᵇ xs) (1ᵇ ys) = sub  (suc (suc n)) xs ys
  sub₁ (suc n) (2ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (sub₁ 1 xs ys)

  -- sub n x y = (x - y) × 2ⁿ
  sub : ℕ → 𝔹 → 𝔹 → 𝔹
  sub zero 0ᵇ      _       = 0ᵇ
  sub (suc n) 0ᵇ      _       = 0ᵇ
  sub zero xs      0ᵇ      = xs
  sub zero (1ᵇ xs) (1ᵇ ys) = sub 1 xs ys
  sub zero (1ᵇ xs) (2ᵇ ys) = 1ᵇ sub₁ 0 xs ys
  sub zero (2ᵇ xs) (1ᵇ ys) = 1ᵇ sub  0 xs ys
  sub zero (2ᵇ xs) (2ᵇ ys) = sub 1 xs ys
  sub (suc n) xs      0ᵇ      = xs ×2^suc n
  sub (suc n) (1ᵇ xs) (1ᵇ ys) = sub (suc (suc n)) xs ys
  sub (suc n) (1ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (sub₁ 1 xs ys)
  sub (suc n) (2ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (sub  1 xs ys)
  sub (suc n) (2ᵇ xs) (2ᵇ ys) = sub (suc (suc n)) xs ys

open import Data.Binary.Order
open import Data.Bool

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = if n ≤ᴮ m then 0ᵇ else sub 0 n m


open import Level
open import Data.Binary.Testers
open import Data.Binary.Conversion.Fast.Strict
open import Path
open import Data.List using (List; _⋯_)
open import Data.List.Sugar using (liftA2)

×2-tester : 𝔹 → ℕ → 𝔹
×2-tester xs zero    = double xs
×2-tester xs (suc n) = double (×2-tester xs n)

test-exp : ℕ → Type
test-exp n = let ns = 0 ⋯ n in
  liftA2 (λ n m → ⟦ n ⇑⟧ ×2^suc m) ns ns ≡
  liftA2 (λ n m → ×2-tester ⟦ n ⇑⟧ m) ns ns

_ : test-exp 30
_ = refl

_ : test _-_ _∸_ 30
_ = refl
