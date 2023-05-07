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

-- ones′ zero    x = x × 2 + 1
-- ones′ (suc n) x = (x + 1) × 2ⁿ

ones′ : ℕ → 𝔹 → 𝔹
ones′ zero    = 1ᵇ_
ones′ (suc n) xs = 2ᵇ ones n xs

zer : ℕ → ℕ
zer zero    = zero
zer (suc _) = suc zero

_×2^suc_ : 𝔹 → ℕ → 𝔹
0ᵇ      ×2^suc n = 0ᵇ
(1ᵇ xs) ×2^suc n = 2ᵇ ones n (double xs)
(2ᵇ xs) ×2^suc n = 2ᵇ ones (suc n) xs

_×2^_ : 𝔹 → ℕ → 𝔹
xs ×2^ zero = xs
xs ×2^ suc n = xs ×2^suc n

mutual
  -- sub₁ x y = (x - (y + 1)) × 2ⁿ
  sub₁ : ℕ → 𝔹 → 𝔹 → 𝔹
  sub₁ n 0ᵇ      _       = ones′ n 0ᵇ
  sub₁ n xs      0ᵇ      = dec xs ×2^ n
  sub₁ n (1ᵇ xs) (1ᵇ ys) = ones′ n (sub₁ (zer n) xs ys)
  sub₁ n (2ᵇ xs) (2ᵇ ys) = ones′ n (sub₁ (zer n) xs ys)
  sub₁ n (1ᵇ xs) (2ᵇ ys) = sub₁ (suc n) xs ys
  sub₁ n (2ᵇ xs) (1ᵇ ys) = sub  (suc n) xs ys

  -- sub n x y = (x - y) × 2ⁿ
  sub : ℕ → 𝔹 → 𝔹 → 𝔹
  sub _ 0ᵇ      _       = 0ᵇ
  sub n xs      0ᵇ      = xs ×2^ n
  sub n (1ᵇ xs) (1ᵇ ys) = sub (suc n) xs ys
  sub n (2ᵇ xs) (2ᵇ ys) = sub (suc n) xs ys
  sub n (1ᵇ xs) (2ᵇ ys) = ones′ n (sub₁ (zer n) xs ys)
  sub n (2ᵇ xs) (1ᵇ ys) = ones′ n (sub  (zer n) xs ys)

open import Data.Binary.Order
open import Data.Bool

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = if n ≤ᴮ m then 0ᵇ else sub 0 n m


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
