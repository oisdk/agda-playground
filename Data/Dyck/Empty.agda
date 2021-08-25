{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Dyck.Empty where

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
  ◇ : Tree A
  [_] : A → Tree A
  _*_ : Tree A → Tree A → Tree A

--------------------------------------------------------------------------------
-- Programs: definition and associated functions
--------------------------------------------------------------------------------

data Prog (A : Type a) : ℕ → Type a where
  halt : Prog A 1
  push : A → Prog A (1 + n) → Prog A n
  pull : Prog A (1 + n) → Prog A (2 + n)
  skip : Prog A (1 + n) → Prog A n

--------------------------------------------------------------------------------
-- Conversion from a Prog to a Tree
--------------------------------------------------------------------------------

prog→tree⊙ : Prog A n → Vec (Tree A) n → Tree A
prog→tree⊙ halt        (v ∷ [])       = v
prog→tree⊙ (push v is) st             = prog→tree⊙ is ([ v ] ∷ st)
prog→tree⊙ (pull   is) (t₁ ∷ t₂ ∷ st) = prog→tree⊙ is (t₂ * t₁ ∷ st)
prog→tree⊙ (skip   is) st             = prog→tree⊙ is (◇ ∷ st)

prog→tree : Prog A zero → Tree A
prog→tree ds = prog→tree⊙ ds []

--------------------------------------------------------------------------------
-- Conversion from a Tree to a Prog
--------------------------------------------------------------------------------

tree→prog⊙ : Tree A → Prog A (suc n) → Prog A n
tree→prog⊙ [ x ]     = push x
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ tree→prog⊙ ys ∘ pull
tree→prog⊙ ◇         = skip

tree→prog : Tree A → Prog A zero
tree→prog tr = tree→prog⊙ tr halt

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

tree→prog→tree⊙ :  {is : Prog A (1 + n)} {st : Vec (Tree A) n} (e : Tree A) →
  prog→tree⊙ (tree→prog⊙ e is) st ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree⊙ [ x ]     = refl
tree→prog→tree⊙ (xs * ys) = tree→prog→tree⊙ xs ; tree→prog→tree⊙ ys
tree→prog→tree⊙ ◇         = refl

prog→tree→prog⊙ :  {st : Vec (Tree A) n} (is : Prog A n) →
 tree→prog (prog→tree⊙ is st) ≡ foldlN (Prog A) tree→prog⊙ is st
prog→tree→prog⊙  halt       = refl
prog→tree→prog⊙ (push i is) = prog→tree→prog⊙ is
prog→tree→prog⊙ (pull   is) = prog→tree→prog⊙ is
prog→tree→prog⊙ (skip   is) = prog→tree→prog⊙ is

prog-iso : Prog A zero ⇔ Tree A
prog-iso .fun = prog→tree
prog-iso .inv = tree→prog
prog-iso .rightInv = tree→prog→tree⊙
prog-iso .leftInv  = prog→tree→prog⊙
