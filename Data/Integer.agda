{-# OPTIONS --cubical --safe #-}

module Data.Integer where

open import Level

open import Data.Nat using (ℕ; suc; zero)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Bool

infixr 9 ⁺_ ⁻suc_ ⁻_
data ℤ : Type₀ where
  ⁺_    : ℕ → ℤ
  ⁻suc_ : ℕ → ℤ

⁻_ : ℕ → ℤ
⁻ zero  = ⁺ zero
⁻ suc n = ⁻suc n

{-# DISPLAY ⁻suc_ n = ⁻ suc n #-}

infixl 6 _+_

_-suc_ : ℕ → ℕ → ℤ
x -suc y =
  if y ℕ.<ᴮ x
    then ⁺_    (x ℕ.∸ (suc y))
    else ⁻suc_ (y ℕ.∸ x)

_+_ : ℤ → ℤ → ℤ
⁺    x + ⁺    y = ⁺ (x ℕ.+ y)
⁺    x + ⁻suc y = x -suc y
⁻suc x + ⁺    y = y -suc x
⁻suc x + ⁻suc y = ⁻suc (suc x ℕ.+ y)

_*-suc_ : ℕ → ℕ → ℤ
zero  *-suc m = ⁺ zero
suc n *-suc m = ⁻suc (n ℕ.+ m ℕ.+ n ℕ.* m)

infixl 7 _*_
_*_ : ℤ → ℤ → ℤ
⁺    x * ⁺    y = ⁺ (x ℕ.* y)
⁺    x * ⁻suc y = x *-suc y
⁻suc x * ⁺    y = y *-suc x
⁻suc x * ⁻suc y = ⁺ (suc x ℕ.* suc y)
