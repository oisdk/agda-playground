{-# OPTIONS --cubical --safe --postfix-projections #-}

module Karatsuba where

open import Prelude
open import Data.List

data Tree {a} (A : Type a) : Type a where
  leaf : A → Tree A
  _⊗_ : Tree A → Tree A → Tree A

record Builder {a} (A : Type a) : Type a where
  field
    shift : ℕ
    lo : Tree A
    hi : Tree A
    out : List A
open Builder

open import Data.Integer
import Data.Nat as ℕ


-- _◆_ : Builder ℤ → Builder ℤ → Builder ℤ
-- (xs ◆ ys) .shift = xs .shift ℕ.+ ys .shift
-- (xs ◆ ys) .lo = xs .lo ⊗ ys .lo
-- (xs ◆ ys) .hi = xs .hi ⊗ ys .hi
-- (xs ◆ ys) .out = {!!}
