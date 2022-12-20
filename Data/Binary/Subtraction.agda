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
  -- sub-exp₁ n x y = (x - (y + 1)) × 2ⁿ⁺¹
  sub-exp₁ : ℕ → 𝔹 → 𝔹 → 𝔹
  sub-exp₁ n 0ᵇ      _       = 2ᵇ ones n 0ᵇ
  sub-exp₁ n (1ᵇ xs) 0ᵇ      = xs ×2^suc suc n
  sub-exp₁ n (2ᵇ xs) 0ᵇ      = 2ᵇ ones n (double xs)
  sub-exp₁ n (1ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (sub-exp₁ 0 xs ys)
  sub-exp₁ n (1ᵇ xs) (2ᵇ ys) = sub-exp₁ (suc n) xs ys
  sub-exp₁ n (2ᵇ xs) (1ᵇ ys) = sub-exp  (suc n) xs ys
  sub-exp₁ n (2ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (sub-exp₁ 0 xs ys)

  -- sub-exp n x y = (x - y) × 2ⁿ⁺¹
  sub-exp : ℕ → 𝔹 → 𝔹 → 𝔹
  sub-exp n xs      0ᵇ      = xs ×2^suc n
  sub-exp n 0ᵇ      _       = 0ᵇ
  sub-exp n (1ᵇ xs) (1ᵇ ys) = sub-exp (suc n) xs ys
  sub-exp n (1ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (sub-exp₁ 0 xs ys)
  sub-exp n (2ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (sub-exp  0 xs ys)
  sub-exp n (2ᵇ xs) (2ᵇ ys) = sub-exp (suc n) xs ys

mutual
  -- sub₁ x y = x - (y + 1)
  sub₁ : 𝔹 → 𝔹 → 𝔹
  sub₁ xs      0ᵇ      = dec xs
  sub₁ 0ᵇ      _       = 1ᵇ 0ᵇ
  sub₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ sub₁ xs ys
  sub₁ (1ᵇ xs) (2ᵇ ys) = sub-exp₁ 0 xs ys
  sub₁ (2ᵇ xs) (1ᵇ ys) = sub-exp  0 xs ys
  sub₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ sub₁ xs ys

  -- sub x y = x - y
  sub : 𝔹 → 𝔹 → 𝔹
  sub 0ᵇ      _       = 0ᵇ
  sub xs      0ᵇ      = xs
  sub (1ᵇ xs) (1ᵇ ys) = sub-exp 0 xs ys
  sub (1ᵇ xs) (2ᵇ ys) = 1ᵇ sub₁ xs ys
  sub (2ᵇ xs) (1ᵇ ys) = 1ᵇ sub  xs ys
  sub (2ᵇ xs) (2ᵇ ys) = sub-exp 0 xs ys

open import Data.Binary.Order
open import Data.Bool

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = if n ≤ᴮ m then 0ᵇ else sub n m


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
