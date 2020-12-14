{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck.Rose where

open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head)
open import Data.Tree.Rose
open import Data.List

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Programs: definition and associated functions
--------------------------------------------------------------------------------

data Prog (A : Type a) : ℕ → Type a where
  halt : Prog A 1
  pull : Prog A (1 + n) → Prog A n
  push : A → Prog A (1 + n) → Prog A (2 + n)

--------------------------------------------------------------------------------
-- Conversion from a Prog to a Tree
--------------------------------------------------------------------------------

prog→tree⊙ : Prog A n → Vec (Forest A) n → Forest A
prog→tree⊙ halt        (v ∷ [])       = v
prog→tree⊙ (pull   is) st             = prog→tree⊙ is ([] ∷ st)
prog→tree⊙ (push v is) (t₁ ∷ t₂ ∷ st) = prog→tree⊙ is (((v & t₂) ∷ t₁) ∷ st)

prog→tree : Prog A zero → Forest A
prog→tree ds = prog→tree⊙ ds []

--------------------------------------------------------------------------------
-- Conversion from a Tree to a Prog
--------------------------------------------------------------------------------

tree→prog⊙ : Forest A → Prog A (suc n) → Prog A n
tree→prog⊙ []              = pull
tree→prog⊙ ((t & ts) ∷ xs) = tree→prog⊙ ts ∘ tree→prog⊙ xs ∘ push t

tree→prog : Forest A → Prog A zero
tree→prog tr = tree→prog⊙ tr halt

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

tree→prog→tree⊙ : (e : Forest A) (is : Prog A (1 + n)) (st : Vec (Forest A) n) →
  prog→tree⊙ (tree→prog⊙ e is) st ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree⊙ []              is st = refl
tree→prog→tree⊙ ((t & ts) ∷ xs) is st =
  tree→prog→tree⊙ ts _ st ; tree→prog→tree⊙ xs (push t is) (ts ∷ st)

tree→prog→tree : (e : Forest A) → prog→tree (tree→prog e) ≡ e
tree→prog→tree e = tree→prog→tree⊙ e halt []

prog→tree→prog⊙ : (is : Prog A n) (st : Vec (Forest A) n) →
 tree→prog (prog→tree⊙ is st) ≡ foldlN (Prog A) tree→prog⊙ is st
prog→tree→prog⊙ halt        st = refl
prog→tree→prog⊙ (pull   is) st = prog→tree→prog⊙ is ([] ∷ st)
prog→tree→prog⊙ (push x is) (t₁ ∷ t₂ ∷ st) =
  prog→tree→prog⊙ is (((x & t₂) ∷ t₁) ∷ st)

prog→tree→prog : (is : Prog A 0) → tree→prog (prog→tree is) ≡ is
prog→tree→prog is = prog→tree→prog⊙ is []

prog-iso : Prog A zero ⇔ Forest A
prog-iso .fun = prog→tree
prog-iso .inv = tree→prog
prog-iso .rightInv = tree→prog→tree
prog-iso .leftInv  = prog→tree→prog
