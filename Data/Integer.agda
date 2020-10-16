{-# OPTIONS --cubical --safe #-}

module Data.Integer where

open import Level

open import Data.Nat using (ℕ; suc; zero)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Bool

data ℤ : Type₀ where
  pos    : ℕ → ℤ
  negsuc : ℕ → ℤ

infixr 9 -_
-_ : ℕ → ℤ
- zero  = pos zero
- suc n = negsuc n

{-# DISPLAY negsuc n = - suc n #-}

infixl 6 _+_

_-suc_ : ℕ → ℕ → ℤ
x -suc y =
  if y ℕ.<ᴮ x
    then pos    (x ℕ.∸ (1 ℕ.+ y))
    else negsuc (y ℕ.∸ x)

_+_ : ℤ → ℤ → ℤ
pos    x + pos    y = pos (x ℕ.+ y)
pos    x + negsuc y = x -suc y
negsuc x + pos    y = y -suc x
negsuc x + negsuc y = negsuc (1 ℕ.+ x ℕ.+ y)

_*-suc_ : ℕ → ℕ → ℤ
zero  *-suc m = pos zero
suc n *-suc m = negsuc (n ℕ.+ m ℕ.+ n ℕ.* m)

infixl 7 _*_
_*_ : ℤ → ℤ → ℤ
pos    x * pos    y = pos (x ℕ.* y)
pos    x * negsuc y = x *-suc y
negsuc x * pos    y = y *-suc x
negsuc x * negsuc y = pos ((1 ℕ.+ x) ℕ.* (1 ℕ.+ y))
