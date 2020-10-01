{-# OPTIONS --cubical --safe #-}

module Data.Binary.Literals where

open import Data.Binary.Definition
open import Data.Binary.Conversion.Strict
open import Literals.Number
open import Data.Unit
open import Data.Nat.Literals

instance
  number𝔹 : Number 𝔹
  Number.Constraint number𝔹 = λ _ → ⊤
  Number.fromNat number𝔹 = λ n → ⟦ n ⇑⟧′
