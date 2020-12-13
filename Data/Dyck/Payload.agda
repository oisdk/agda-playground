{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck.Payload where

open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions
--------------------------------------------------------------------------------

data Tree (A : Type a) : Type a where
  [_] : A → Tree A
  _*_ : Tree A → Tree A → Tree A

--------------------------------------------------------------------------------
-- Programs: definition and associated functions
--------------------------------------------------------------------------------

data Prog (A : Type a) : ℕ → Type a where
  halt : Prog A 1
  push : A → Prog A (1 + n) → Prog A n
  pull : Prog A (1 + n) → Prog A (2 + n)

--------------------------------------------------------------------------------
-- Conversion from a Prog to a Tree
--------------------------------------------------------------------------------

prog→tree⊙ : Prog A n → Vec (Tree A) n → Tree A
prog→tree⊙ halt        (v ∷ [])       = v
prog→tree⊙ (push v is) st             = prog→tree⊙ is ([ v ] ∷ st)
prog→tree⊙ (pull   is) (t₁ ∷ t₂ ∷ st) = prog→tree⊙ is (t₂ * t₁ ∷ st)

prog→tree : Prog A zero → Tree A
prog→tree ds = prog→tree⊙ ds []

--------------------------------------------------------------------------------
-- Conversion from a Tree to a Prog
--------------------------------------------------------------------------------

tree→prog⊙ : Tree A → Prog A (suc n) → Prog A n
tree→prog⊙ [ x ]     = push x
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ tree→prog⊙ ys ∘ pull

tree→prog : Tree A → Prog A zero
tree→prog tr = tree→prog⊙ tr halt

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

tree→prog→tree⊙ : (e : Tree A) (is : Prog A (1 + n)) (st : Vec (Tree A) n) →
  prog→tree⊙ (tree→prog⊙ e is) st ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree⊙ [ x ]     is st = refl
tree→prog→tree⊙ (xs * ys) is st = tree→prog→tree⊙ xs _ st ;
                                  tree→prog→tree⊙ ys (pull is) (xs ∷ st)

tree→prog→tree : (e : Tree A) → prog→tree (tree→prog e) ≡ e
tree→prog→tree e = tree→prog→tree⊙ e halt []

prog→tree→prog⊙ : (is : Prog A n) (st : Vec (Tree A) n) →
 tree→prog (prog→tree⊙ is st) ≡ foldlN (Prog A) tree→prog⊙ is st
prog→tree→prog⊙  halt       st = refl
prog→tree→prog⊙ (push i is) st = prog→tree→prog⊙ is ([ i ] ∷ st)
prog→tree→prog⊙ (pull is) (t₁ ∷ t₂ ∷ ts) = prog→tree→prog⊙ is ((t₂ * t₁) ∷ ts)

prog→tree→prog : (is : Prog A 0) → tree→prog (prog→tree is) ≡ is
prog→tree→prog is = prog→tree→prog⊙ is []

prog-iso : Prog A zero ⇔ Tree A
prog-iso .fun = prog→tree
prog-iso .inv = tree→prog
prog-iso .rightInv = tree→prog→tree
prog-iso .leftInv  = prog→tree→prog
