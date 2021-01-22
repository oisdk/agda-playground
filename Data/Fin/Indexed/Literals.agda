{-# OPTIONS --without-K --safe #-}

module Data.Fin.Indexed.Literals where

-- import Data.Nat as ℕ
-- import Data.Nat.Properties as ℕ
open import Data.Fin.Indexed.Base
open import Data.Fin.Indexed.Properties
open import Literals.Number
-- open import Relation.Nullary
open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_)
open import Data.Bool
open import Agda.Builtin.Nat using (_<_)

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = record
    { Constraint = λ m → T (m <ᵇ n)
    ; fromNat    = λ m {{pr}} → FinFromℕ {n} m pr
    }
