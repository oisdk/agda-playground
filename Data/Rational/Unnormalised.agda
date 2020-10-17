{-# OPTIONS --cubical --safe #-}

module Data.Rational.Unnormalised where

open import Prelude
open import Data.Integer using (ℤ; pos)
import Data.Integer as ℤ
import Data.Nat as ℕ

record ℚ : Type₀ where
  constructor _/_+1
  field
    num : ℤ
    pred⟨den⟩ : ℕ

  den : ℕ
  den = 1 ℕ.+ pred⟨den⟩
open ℚ public



infixl 6 _+_
_+_ : ℚ → ℚ → ℚ
num       (x + y) = num x ℤ.* pos (den y) ℤ.+ num y ℤ.* pos (den x)
pred⟨den⟩ (_ / x +1 + _ / y +1) = x ℕ.* y ℕ.+ x ℕ.+ y


--   (x  + - 1) * (y + - 1) - 1
-- = y(x - 1) - (x - 1) - 1
-- xy - y - x + 1 - 1
-- xy - y - x
