{-# OPTIONS --cubical --safe #-}

module Data.Nat.Literals where

open import Data.Nat
open import Literals.Number
open import Data.Unit

instance
  numberNat : Number ℕ
  numberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → n
    }
