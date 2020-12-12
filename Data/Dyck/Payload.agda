{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck.Payload where

open import Prelude
open import Data.List using (List; _∷_; []; _++_; length)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Function.Surjective
open import Function.Injective
open import Function.Injective.Properties using (inject-contrapositive)
open import Data.Nat.Properties using (snotz; znots; pred)
open import Data.Vec.Iterated

private
  variable
    n m k : ℕ

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions
--------------------------------------------------------------------------------

data Tree (A : Type a) : Type a where
  [_] : A → Tree A
  _*_ : Tree A → Tree A → Tree A

--------------------------------------------------------------------------------
-- Programs: definition and associated functions
--------------------------------------------------------------------------------

data Prog {a} (A : Type a) : ℕ → Type a where
  halt : Prog A 1
  push : A → Prog A (1 + n) → Prog A n
  pull : Prog A (1 + n) → Prog A (2 + n)

module _{p} (P : ℕ → Type p)
            (lb : ∀ {n} → P (2 + n) → P (1 + n))
            (rb : ∀ {n} → A → P n → P (1 + n))
            where
  foldlProg : P n → Prog A n → P 1
  foldlProg bs halt = bs
  foldlProg bs (push x xs) = foldlProg (rb x bs) xs
  foldlProg bs (pull   xs) = foldlProg (lb   bs) xs
-- In terms of foldr:
-- foldlProg P lb rb bs xs = foldrProg (λ n → P n → P zero) (λ x k bs → k (rb x bs)) (λ k bs → k (lb bs)) id xs bs

--------------------------------------------------------------------------------
-- Conversion from a Prog to a Tree
--------------------------------------------------------------------------------

reduce : Vec (Tree A) (2 + n) → Vec (Tree A) (1 + n)
reduce (t₁ ∷ t₂ ∷ s) = (t₂ * t₁) ∷ s

shift : A → Vec (Tree A) n → Vec (Tree A) (1 + n)
shift x s = [ x ] ∷ s

prog→tree⊙ : Prog A n → Vec (Tree A) n → Vec (Tree A) 1
prog→tree⊙ p s = foldlProg (λ n → Vec (Tree _) n) reduce shift s p

prog→tree : Prog A zero → Tree A
prog→tree ds = head (prog→tree⊙ ds [])

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

tree→prog→tree⊙ : (e : Tree A) (is : Prog A (1 + n)) (st : Vec (Tree A) n) → prog→tree⊙ (tree→prog⊙ e is) st ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree⊙ [ x ]     is st = refl
tree→prog→tree⊙ (xs * ys) is st = tree→prog→tree⊙ xs _ st ; tree→prog→tree⊙ ys (pull is) (xs ∷ st)

tree→prog→tree : (t : Tree A) → prog→tree (tree→prog t) ≡ t
tree→prog→tree t = cong head (tree→prog→tree⊙ t halt [])

prog→tree→prog⊙ : (vs : Vec (Tree A) n) (xs : Prog A n) → tree→prog (head (prog→tree⊙ xs vs)) ≡ foldlN (Prog A) tree→prog⊙ xs vs
prog→tree→prog⊙ vs  halt       = refl
prog→tree→prog⊙ vs (push x xs) = prog→tree→prog⊙ (shift x vs) xs
prog→tree→prog⊙ vs (pull   xs) = prog→tree→prog⊙ (reduce  vs) xs

prog→tree→prog : (xs : Prog A 0) → tree→prog (prog→tree xs) ≡ xs
prog→tree→prog = prog→tree→prog⊙ []

prog-iso : Prog A zero ⇔ Tree A
prog-iso .fun = prog→tree
prog-iso .inv = tree→prog
prog-iso .rightInv = tree→prog→tree
prog-iso .leftInv  = prog→tree→prog
