module Data.Fin.Sigma where

open import Prelude
open import Data.Nat
open import Data.Nat.Properties

Fin : ℕ → Type
Fin n = ∃ m × (m < n)

open import Data.List

_!!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) !! (zero  , p) = x
(x ∷ xs) !! (suc n , p) = xs !! (n , p)
