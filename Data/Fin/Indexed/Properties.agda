{-# OPTIONS --without-K --safe #-}

module Data.Fin.Indexed.Properties where

open import Agda.Builtin.Nat using (_<_)
open import Data.Nat.Base
open import Data.Fin.Indexed.Base
open import Data.Bool

FinFromℕ : ∀ {m} → (n : ℕ) → T (n < m) → Fin m
FinFromℕ {m = suc m} zero    p = f0
FinFromℕ {m = suc m} (suc n) p = fs (FinFromℕ n p)

FinToℕ : ∀ {n} → Fin n → ℕ
FinToℕ f0     = zero
FinToℕ (fs x) = suc (FinToℕ x)

weaken : ∀ {n} → Fin n → Fin (suc n)
weaken {suc n} f0 = f0
weaken {suc n} (fs x) = fs (weaken x)
