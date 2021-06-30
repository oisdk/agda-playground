{-# OPTIONS --cubical --safe #-}

module Data.Nat.WellFounded where

open import Prelude
open import Data.Nat
open import WellFounded

infix 4 _≤_ _<_
data _≤_ (n : ℕ) : ℕ → Type where
  n≤n : n ≤ n
  n≤s : ∀ {m} → n ≤ m → n ≤ suc m

_<_ : ℕ → ℕ → Type
n < m = suc n ≤ m

≤-wellFounded : WellFounded _<_
≤-wellFounded x = acc (go x)
  where
  go : ∀ n m → m < n → Acc _<_ m
  go (suc n) .n n≤n = acc (go n)
  go (suc n) m (n≤s m<n) = go n m m<n

open import Data.Nat.DivMod
open import Agda.Builtin.Nat using (div-helper)
import Data.Nat.Properties as ℕ

-- Bear in mind the following two functions will not compute
-- as currently subst (with --cubical) doesn't work on GADTs.
--
-- We could write the functions without using subst.
div2≤ : ∀ n → n ÷ 2 ≤ n
div2≤ n = subst (n ÷ 2 ≤_) (ℕ.+-idʳ n) (go zero n)
  where
  go : ∀ k n → div-helper k 1 n 1 ≤ n + k
  go k zero = n≤n
  go k (suc zero) = n≤s n≤n
  go k (suc (suc n)) = n≤s (subst (div-helper (suc k) 1 n 1 ≤_) (ℕ.+-suc n k) (go (suc k) n))

s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m
s≤s n≤n = n≤n
s≤s (n≤s x) = n≤s (s≤s x)
