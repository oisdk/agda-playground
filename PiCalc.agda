module PiCalc where

open import Prelude
open import Data.Nat.Order
open import Data.Nat.Properties

Fin : ℕ → Type
Fin n = ∃ m × (m < n)

data Term (n : ℕ) : Type where
  `ν : Term (suc n) → Term n
  _↓_·_ : Fin n → Fin n → Term n → Term n
  _↑_·_ : Fin n → Fin n → Term n → Term n
  _`∣_ : Term n → Term n → Term n
  `! : Term n → Term n
  𝟘 : Term n

private
  variable n m : ℕ


fs : Fin n → Fin (suc n)
fs (n , p) = suc n , p

ext : (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
ext ρ (zero  , p) = zero , p
ext ρ (suc n , p) = fs (ρ (n , p))

rename : (Fin n → Fin m) → Term n → Term m
rename ρ (`ν x) = `ν (rename (ext ρ) x)
rename ρ (x ↓ y · xs) = ρ x ↓ ρ y · rename ρ xs
rename ρ (x ↑ y · xs) = ρ x ↑ ρ y · rename ρ xs
rename ρ (x `∣ y) = rename ρ x `∣ rename ρ y
rename ρ (`! x) = `! (rename ρ x)
rename ρ 𝟘 = 𝟘
