{-# OPTIONS --without-K --safe #-}

module Data.Fin.Indexed.Properties where

open import Agda.Builtin.Nat using (_<_)
open import Data.Nat.Base
open import Data.Fin.Indexed.Base
open import Data.Bool
open import Data.Maybe.Base

private variable n m : ℕ

FinFromℕ : ∀ {m} → (n : ℕ) → T (n < m) → Fin m
FinFromℕ {m = suc m} zero    p = f0
FinFromℕ {m = suc m} (suc n) p = fs (FinFromℕ n p)

weaken : ∀ {n} → Fin n → Fin (suc n)
weaken {suc n} f0 = f0
weaken {suc n} (fs x) = fs (weaken x)

-- x \\ y | x < y = just x
--        | x ≡ y = nothing
--        | x > y = just (x - 1)
_\\_ : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
f0   \\ f0   = nothing
fs i \\ f0   = just i
_\\_ {suc n} (fs i) (fs j) = mapMaybe fs (i \\ j)
_\\_ {suc n} (f0  ) (fs j) = just f0
