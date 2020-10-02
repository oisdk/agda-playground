{-# OPTIONS --cubical --safe #-}

module Data.Tree.Braun where

open import Prelude
open import Data.Nat

data Bal (n : ℕ) : ℕ → ℕ → Type₀ where
  one : Bal n n       (1 + n * 2)
  two : Bal n (suc n) (2 + n * 2)

data Tree {a} (A : Type a) : ℕ → Type a where
  leaf : Tree A 0
  node : ∀ {n m r} → (bal : Bal n m r) → A → (ls : Tree A m) → (rs : Tree A n) → Tree A r

private
  variable
    n : ℕ

inc : A → Tree A n → Tree A (suc n)
inc x leaf = node one x leaf leaf
inc x (node one y ls rs) = node two x (inc y rs) ls
inc x (node two y ls rs) = node one x (inc y rs) ls
