{-# OPTIONS --without-K --safe #-}

module Data.Fin.Indexed.Base where

open import Data.Nat using (ℕ; suc; zero)
open import Agda.Builtin.Nat using (_<_)
open import Level
open import Data.Bool.Truth

private variable n m : ℕ

-- This is the more traditional definition of Fin,
-- that you would usually find in Agda code.
-- I tend to use the other one because cubical
-- Agda doesn't yet support transport along
-- equalities of indexed types.
data Fin : ℕ → Type₀ where
  f0 : Fin (suc n)
  fs : Fin n → Fin (suc n)

FinToℕ : Fin n → ℕ
FinToℕ f0 = zero
FinToℕ (fs i) = suc (FinToℕ i)

{-# DISPLAY f0 = zero #-}
{-# DISPLAY fs n = suc n #-}

FinFromℕ : ∀ {m} → (n : ℕ) → T (n < m) → Fin m
FinFromℕ {m = suc m} zero    p = f0
FinFromℕ {m = suc m} (suc n) p = fs (FinFromℕ n p)
