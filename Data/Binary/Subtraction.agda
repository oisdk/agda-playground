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

_×2^_ : 𝔹 → ℕ → 𝔹
xs ×2^ zero  = xs
xs ×2^ suc n = xs ×2^suc n

_-1×2^suc_ : 𝔹 → ℕ → 𝔹
0ᵇ      -1×2^suc _ = 0ᵇ
(2ᵇ xs) -1×2^suc n = 2ᵇ ones n (double xs)
(1ᵇ xs) -1×2^suc n = xs ×2^suc suc n

mutual
  -- sube₁ n x y = (x - (y + 1)) × 2ⁿ⁺¹
  sube₁ : ℕ → 𝔹 → 𝔹 → 𝔹
  sube₁ n 0ᵇ      _       = 0ᵇ
  sube₁ n xs      0ᵇ      = xs -1×2^suc n
  sube₁ n (1ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (sube₁ 0 xs ys)
  sube₁ n (2ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (sube₁ 0 xs ys)
  sube₁ n (1ᵇ xs) (2ᵇ ys) = sube₁ (suc n) xs ys
  sube₁ n (2ᵇ xs) (1ᵇ ys) = sube  (suc n) xs ys

  -- sube n x y = (x - y) × 2ⁿ⁺¹
  sube : ℕ → 𝔹 → 𝔹 → 𝔹
  sube _ 0ᵇ      _       = 0ᵇ
  sube n xs      0ᵇ      = xs ×2^suc n
  sube n (1ᵇ xs) (1ᵇ ys) = sube (suc n) xs ys
  sube n (2ᵇ xs) (2ᵇ ys) = sube (suc n) xs ys
  sube n (1ᵇ xs) (2ᵇ ys) = 2ᵇ ones n (sube₁ 0 xs ys)
  sube n (2ᵇ xs) (1ᵇ ys) = 2ᵇ ones n (sube  0 xs ys)

mutual
  -- sub₁ x y = x - (y + 1)
  sub₁ : 𝔹 → 𝔹 → 𝔹
  sub₁ 0ᵇ      _       = 0ᵇ
  sub₁ xs      0ᵇ      = dec xs
  sub₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ sub₁ xs ys
  sub₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ sub₁ xs ys
  sub₁ (1ᵇ xs) (2ᵇ ys) = sube₁ 0 xs ys
  sub₁ (2ᵇ xs) (1ᵇ ys) = sube  0 xs ys

  -- sub x y = x - y
  sub : 𝔹 → 𝔹 → 𝔹
  sub 0ᵇ      _       = 0ᵇ
  sub xs      0ᵇ      = xs
  sub (1ᵇ xs) (1ᵇ ys) = sube 0 xs ys
  sub (2ᵇ xs) (2ᵇ ys) = sube 0 xs ys
  sub (1ᵇ xs) (2ᵇ ys) = 1ᵇ sub₁ xs ys
  sub (2ᵇ xs) (1ᵇ ys) = 1ᵇ sub  xs ys

open import Data.Binary.Order
open import Data.Bool

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = if n ≤ᴮ m then 0ᵇ else sub n m

open import Level
open import Data.Binary.Testers
open import Data.Binary.Conversion.Fast.Strict
open import Data.Binary.Conversion using (⟦_⇓⟧)
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

-- e : ℕ → ℕ → ℕ
-- e n m = ⟦ ones′ n ⟦ m ⇑⟧ ⇓⟧

-- e′ : ℕ → ℕ → ℕ
-- e′ n m = ⟦ ×2-tester ⟦ m ⇑⟧ (pred n) ⇓⟧ + {!!}
-- e′ zero    m = suc ⟦ double ⟦ m ⇑⟧ ⇓⟧
-- e′ (suc n) m = ⟦ ×2-tester ⟦ suc m ⇑⟧ n ⇓⟧

-- test-e : ℕ → Type
-- test-e n = let ns = 0 ⋯ n in
--   liftA2 e ns ns ≡
--   liftA2 e′ ns ns

_ : test-exp 30
_ = refl

_ : test _-_ _∸_ 30
_ = refl

-- _ : e 1 3 ≡ e′ 1 3
-- _ = refl


-- _ : test-e 30
-- _ = refl
