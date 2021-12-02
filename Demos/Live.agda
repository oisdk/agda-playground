{-# OPTIONS --guardedness #-}

module Demos.Live where

open import Prelude
open import Data.Nat using (_+_)

-- Stream : Type a → Type a
-- Stream A = ℕ → A

-- ones : Stream ℕ
-- ones zero    = 1
-- ones (suc n) = ones n

-- head : Stream A → A
-- head xs = xs zero

-- tail : Stream A → Stream A
-- tail xs n = xs (suc n)

-- data Stream a = a :< Stream a

record Stream (A : Type a) : Type a where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

adds : Stream ℕ → Stream ℕ → Stream ℕ
head (adds xs ys) = head xs + head ys
tail (adds xs ys) = adds (tail xs) (tail ys)

{-# TERMINATING #-}
fibs : Stream ℕ
head fibs = 0
head (tail fibs) = 1
tail (tail fibs) = adds fibs (tail fibs)

ind : ℕ → Stream A → A
ind zero    = head
ind (suc n) = ind n ∘ tail
