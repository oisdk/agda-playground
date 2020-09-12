{-# OPTIONS --cubical --safe #-}

module Data.Fin.Literals where

-- import Data.Nat as ℕ
-- import Data.Nat.Properties as ℕ
open import Data.Fin
open import Data.Fin.Properties
open import Literals.Number
-- open import Relation.Nullary
open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_)
open import Data.Bool

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = record
    { Constraint = λ m → T (m <ᵇ n)
    ; fromNat    = λ m {{pr}} → FinFromℕ m n pr
    }
