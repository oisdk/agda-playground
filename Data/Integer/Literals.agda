{-# OPTIONS --cubical --safe #-}

module Data.Integer.Literals where

open import Data.Integer
open import Literals.Number
open import Data.Unit

instance
  numberNat : Number ℤ
  numberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → ⁺ n
    }
