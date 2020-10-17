{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Rational.Unnormalised where

open import Prelude
open import Data.Integer using (ℤ; pos)
import Data.Integer as ℤ
import Data.Nat as ℕ
open import Data.Nat.DivMod using (nonZero)

record ℚ : Type₀ where
  constructor _/_+1
  field
    num : ℤ
    den-pred : ℕ

  den : ℕ
  den = 1 ℕ.+ den-pred
open ℚ public

_/_ : (n : ℤ) → (d : ℕ) → ⦃ d≢0 : T (nonZero d) ⦄ → ℚ
n / suc d = n / d +1

{-# DISPLAY _/_+1 n d = n / suc d #-}

infixl 6 _+_
_+_ : ℚ → ℚ → ℚ
(x + y) .num = num x ℤ.* pos (den y) ℤ.+ num y ℤ.* pos (den x)
(x + y) .den-pred = x .den-pred ℕ.+ y .den-pred ℕ.+ x .den-pred ℕ.* y .den-pred


infixl 7 _*_
_*_ : ℚ → ℚ → ℚ
(x * y) .num = x .num ℤ.* y .num
(x * y) .den-pred = x .den-pred ℕ.+ y .den-pred ℕ.+ x .den-pred ℕ.* y .den-pred
