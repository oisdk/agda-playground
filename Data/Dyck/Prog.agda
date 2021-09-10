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

private variable n : ℕ

--------------------------------------------------------------------------------
-- We have 2 forms that we want to convert between: an AST and a flat code.
--------------------------------------------------------------------------------

data Expr : Type where
  [_] : ℕ → Expr
  _⊕_ : Expr → Expr → Expr

--------------------------------------------------------------------------------
-- We do the conversion with cayley forms of the dyck monoids
--------------------------------------------------------------------------------

⟨_⟩_↝_ : (ℕ → Type) → ℕ → ℕ → Type
⟨ C ⟩ n ↝ m = ∀ {i} → C (n + i) → C (m + i)

--------------------------------------------------------------------------------
-- An encoding of an AST
--------------------------------------------------------------------------------

data Code : ℕ → Type where
  HALT : Code 1
  PUSH : ℕ → ⟨ Code ⟩ 1 ↝ 0
  ADD  :     ⟨ Code ⟩ 1 ↝ 2

--------------------------------------------------------------------------------
-- We will need a stack (a snoc-list)
--------------------------------------------------------------------------------

Stack : Type → ℕ → Type
Stack A zero    = ⊤
Stack A (suc n) = Stack A n × A

infixl 5 _∷_
pattern _∷_ xs x = xs , x

foldl : (P : ℕ → Type) → (A → ⟨ P ⟩ 1 ↝ 0) → Stack A n → P n → P zero
foldl {n = zero}  P f tt       = id
foldl {n = suc n} P f (xs ∷ x) = foldl P f xs ∘ f x

private variable st : Stack Expr n

--------------------------------------------------------------------------------
-- Conversion to and from code
--------------------------------------------------------------------------------

--            Code n → ⟨ Stack Expr ⟩ n ↝ 1
code→expr⊙ : Code n → Stack Expr n → Expr
code→expr⊙ HALT        (tt ∷ e)       = e
code→expr⊙ (PUSH v is) st             = code→expr⊙ is (st ∷ [ v ])
code→expr⊙ (ADD is)    (st ∷ xs ∷ ys) = code→expr⊙ is (st ∷ xs ⊕ ys)

code→expr : Code 0 → Expr
code→expr ds = code→expr⊙ ds tt

expr→code⊙ : Expr → ⟨ Code ⟩ 1 ↝ 0
expr→code⊙ [ x ]     = PUSH x
expr→code⊙ (xs ⊕ ys) = expr→code⊙ xs ∘ expr→code⊙ ys ∘ ADD

expr→code : Expr → Code 0
expr→code xs = expr→code⊙ xs HALT

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

expr→code→expr⊙ : {is : Code (1 + n)} (e : Expr) →
  code→expr⊙ (expr→code⊙ e is) st ≡ code→expr⊙ is (st ∷ e)
expr→code→expr⊙ [ x ]     = refl
expr→code→expr⊙ (xs ⊕ ys) = expr→code→expr⊙ xs ; expr→code→expr⊙ ys

code→expr→code⊙ : (is : Code n) →
 expr→code (code→expr⊙ is st) ≡ foldl Code expr→code⊙ st is
code→expr→code⊙  HALT       = refl
code→expr→code⊙ (PUSH i is) = code→expr→code⊙ is
code→expr→code⊙ (ADD    is) = code→expr→code⊙ is

prog-iso : Code 0 ⇔ Expr
prog-iso .fun = code→expr
prog-iso .inv = expr→code
prog-iso .rightInv = expr→code→expr⊙
prog-iso .leftInv  = code→expr→code⊙
