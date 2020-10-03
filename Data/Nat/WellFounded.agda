{-# OPTIONS --cubical --safe #-}

module Data.Nat.WellFounded where

open import Prelude
open import Data.Nat
open import WellFounded

infix 4 _≤_ _<_
data _≤_ (n : ℕ) : ℕ → Type₀ where
  n≤n : n ≤ n
  n≤p : ∀ {m} → n ≤ m → n ≤ suc m

_<_ : ℕ → ℕ → Type₀
n < m = suc n ≤ m

≤-wellFounded : WellFounded _<_
≤-wellFounded x = acc (go x)
  where
  go : ∀ n m → m < n → Acc _<_ m
  go (suc n) .n n≤n = acc (go n)
  go (suc n) m (n≤p m<n) = go n m m<n
