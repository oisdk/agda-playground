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
≤-wellFounded = acc ∘ go
  where
  go : ∀ n m → m < n → Acc _<_ m
  go (suc n) .n n≤n = acc (go n)
  go (suc n) m (n≤s m<n) = go n m m<n

open import Data.Nat.DivMod
open import Agda.Builtin.Nat using (div-helper)
import Data.Nat.Properties as ℕ


private module ComputingSubstOnℕ where
  infix 4 _≡ℕ_
  _≡ℕ_ : ℕ → ℕ → Type
  n ≡ℕ m = T (n ℕ.Eqℕ.≡ᴮ m)

  substℕ : ∀ (P : ℕ → Type) {n m} → n ≡ℕ m → P n → P m
  substℕ P {zero}  {zero } p = id
  substℕ P {suc n} {suc m} p = substℕ (P ∘ suc) p

  +0ℕ : ∀ n → n + zero ≡ℕ n
  +0ℕ zero = tt
  +0ℕ (suc n) = +0ℕ n

  +sucℕ : ∀ n m → n + suc m ≡ℕ suc (n + m)
  +sucℕ zero zero = tt
  +sucℕ zero (suc n) = +sucℕ zero n
  +sucℕ (suc n) m = +sucℕ n m

open ComputingSubstOnℕ

div2≤ : ∀ n → n ÷ 2 ≤ n
div2≤ n = substℕ (n ÷ 2 ≤_) (+0ℕ n) (go zero n)
  where
  go : ∀ k n → div-helper k 1 n 1 ≤ n + k
  go k zero = n≤n
  go k (suc zero) = n≤s n≤n
  go k (suc (suc n)) = n≤s (substℕ (div-helper (suc k) 1 n 1 ≤_) (+sucℕ n k) (go (suc k) n))


s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m
s≤s n≤n = n≤n
s≤s (n≤s x) = n≤s (s≤s x)
