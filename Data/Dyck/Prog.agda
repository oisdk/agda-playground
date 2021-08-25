{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This file contains an implementation of the stack-based compiler for Hutton's
-- razor, as from:
--
--   P. Bahr and G. Hutton, “Calculating correct compilers,” Journal of
--   Functional Programming, vol. 25, no. e14, Sep. 2015,
--   doi: 10.1017/S0956796815000180.
--
-- The compiler is total and the evaluator is stack-safe, and furthermore we have
-- proven a full isomorphism between the code representation and the AST.

module Data.Dyck.Prog where

open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head)

private variable n : ℕ

--------------------------------------------------------------------------------
-- Language for Arithmetic Expressions
--------------------------------------------------------------------------------

data Expr : Type where
  [_] : ℕ → Expr
  _⊕_ : Expr → Expr → Expr

--------------------------------------------------------------------------------
-- Code for the virtual stack machine.
--------------------------------------------------------------------------------

mutual
  -- A function from n arguments to m results
  _⇨_ : ℕ → ℕ → Type
  n ⇨ m = ∀ {i} → Code (m + i) → Code (n + i)

  data Code : ℕ → Type where
    HALT : Code 1
    PUSH : ℕ → 0 ⇨ 1
    ADD  : 2 ⇨ 1

--------------------------------------------------------------------------------
-- Conversion from a Code to a Expr (evaluation / execution)
--------------------------------------------------------------------------------

code→expr⊙ : Code n → Vec Expr n → Expr
code→expr⊙ HALT        (v ∷ [])       = v
code→expr⊙ (PUSH v is) st             = code→expr⊙ is ([ v ] ∷ st)
code→expr⊙ (ADD    is) (t₁ ∷ t₂ ∷ st) = code→expr⊙ is (t₂ ⊕ t₁ ∷ st)

code→expr : Code zero → Expr
code→expr ds = code→expr⊙ ds []

--------------------------------------------------------------------------------
-- Conversion from a Expr to a Code (compilation)
--------------------------------------------------------------------------------

expr→code⊙ : Expr → 0 ⇨ 1
expr→code⊙ [ x ]     = PUSH x
expr→code⊙ (xs ⊕ ys) = expr→code⊙ xs ∘ expr→code⊙ ys ∘ ADD

expr→code : Expr → Code 0
expr→code tr = expr→code⊙ tr HALT

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

expr→code→expr⊙ : {is : Code (1 + n)} {st : Vec Expr n} (e : Expr) →
  code→expr⊙ (expr→code⊙ e is) st ≡ code→expr⊙ is (e ∷ st)
expr→code→expr⊙ [ x ]     = refl
expr→code→expr⊙ (xs ⊕ ys) = expr→code→expr⊙ xs ; expr→code→expr⊙ ys

code→expr→code⊙ : {st : Vec Expr n} (is : Code n) →
 expr→code (code→expr⊙ is st) ≡ foldlN Code (λ x xs → expr→code⊙ x xs) is st
code→expr→code⊙  HALT       = refl
code→expr→code⊙ (PUSH i is) = code→expr→code⊙ is
code→expr→code⊙ (ADD    is) = code→expr→code⊙ is

prog-iso : Code 0 ⇔ Expr
prog-iso .fun = code→expr
prog-iso .inv = expr→code
prog-iso .rightInv = expr→code→expr⊙
prog-iso .leftInv  = code→expr→code⊙
