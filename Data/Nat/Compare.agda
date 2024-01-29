{-# OPTIONS --safe #-}

module Data.Nat.Compare where

open import Data.Nat.Base
open import Data.Maybe
open import Data.Bool
open import Level
open import Data.Sigma
open import Path

Ordering : Type
Ordering = Maybe (Bool × ℕ)

pattern equal = nothing
pattern less n = just (false , n)
pattern greater n = just (true , n)

compare : ℕ → ℕ → Ordering
compare zero zero = equal
compare zero (suc m) = less m
compare (suc n) zero = greater n
compare (suc n) (suc m) = compare n m

Compared : ℕ → ℕ → Ordering → Type
Compared x y (less    n) = suc x + n ≡ y
Compared x y (greater n) = suc y + n ≡ x
Compared x y equal       = x ≡ y

suc-compared : ∀ x y z → Compared x y z → Compared (suc x) (suc y) z
suc-compared x y (less _)    = cong suc
suc-compared x y (greater _) = cong suc
suc-compared x y equal       = cong suc

comparing : ∀ x y → Compared x y (compare x y)
comparing zero    zero    = refl
comparing zero    (suc y) = refl
comparing (suc x) zero    = refl
comparing (suc x) (suc y) = suc-compared x y _ (comparing x y)

