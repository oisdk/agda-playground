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

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Language for Arithmetic Expressions
--------------------------------------------------------------------------------

data Expr (A : Type a) : Type a where
  [_] : A → Expr A
  _⊕_ : Expr A → Expr A → Expr A

--------------------------------------------------------------------------------
-- Code for the virtual stack machine.
--------------------------------------------------------------------------------

data Code (A : Type a) : ℕ → Type a where
  HALT : Code A 1
  PUSH : A → Code A (1 + n) → Code A n
  ADD  : Code A (1 + n) → Code A (2 + n)

--------------------------------------------------------------------------------
-- Conversion from a Code to a Expr (evaluation / execution)
--------------------------------------------------------------------------------

code→expr⊙ : Code A n → Vec (Expr A) n → Expr A
code→expr⊙ HALT        (v ∷ [])       = v
code→expr⊙ (PUSH v is) st             = code→expr⊙ is ([ v ] ∷ st)
code→expr⊙ (ADD    is) (t₁ ∷ t₂ ∷ st) = code→expr⊙ is (t₂ ⊕ t₁ ∷ st)

code→expr : Code A zero → Expr A
code→expr ds = code→expr⊙ ds []

--------------------------------------------------------------------------------
-- Conversion from a Expr to a Code (compilation)
--------------------------------------------------------------------------------

expr→code⊙ : Expr A → Code A (1 + n) → Code A n
expr→code⊙ [ x ]     = PUSH x
expr→code⊙ (xs ⊕ ys) = expr→code⊙ xs ∘ expr→code⊙ ys ∘ ADD

expr→code : Expr A → Code A 0
expr→code tr = expr→code⊙ tr HALT

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

expr→code→expr⊙ : {is : Code A (1 + n)} {st : Vec (Expr A) n} (e : Expr A) →
  code→expr⊙ (expr→code⊙ e is) st ≡ code→expr⊙ is (e ∷ st)
expr→code→expr⊙ [ x ]     = refl
expr→code→expr⊙ (xs ⊕ ys) = expr→code→expr⊙ xs ; expr→code→expr⊙ ys

code→expr→code⊙ : {st : Vec (Expr A) n} (is : Code A n) →
 expr→code (code→expr⊙ is st) ≡ foldlN (Code A) expr→code⊙ is st
code→expr→code⊙  HALT       = refl
code→expr→code⊙ (PUSH i is) = code→expr→code⊙ is
code→expr→code⊙ (ADD    is) = code→expr→code⊙ is

prog-iso : Code A 0 ⇔ Expr A
prog-iso .fun = code→expr
prog-iso .inv = expr→code
prog-iso .rightInv = expr→code→expr⊙
prog-iso .leftInv  = code→expr→code⊙
