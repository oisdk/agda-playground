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
-- We will need a stack (a snoc-list)
--------------------------------------------------------------------------------

Stack : Type → ℕ → Type
Stack A zero    = ⊤
Stack A (suc n) = Stack A n × A

infixl 5 _∷_
pattern _∷_ xs x = xs , x

foldl : (P : ℕ → Type) → (A → ⟨ P ⟩ 1 ↝ 0) → Stack A n → P n → P zero
foldl {n = zero}  P f xs       = id
foldl {n = suc n} P f (xs ∷ x) = foldl P f xs ∘ f x

--------------------------------------------------------------------------------
-- Operations on a stack machine
--------------------------------------------------------------------------------

push : Expr → ⟨ Stack Expr ⟩ 0 ↝ 1
push v st = st ∷ v

add : ⟨ Stack Expr ⟩ 2 ↝ 1
add (st ∷ t₁ ∷ t₂) = st ∷ t₁ ⊕ t₂

data Code : ℕ → Type where
  HALT : Code 1
  PUSH : ℕ → ⟨ Code ⟩ 1 ↝ 0
  ADD  : ⟨ Code ⟩ 1 ↝ 2

--------------------------------------------------------------------------------
-- Conversion from a Code to a Expr (evaluation / execution)
--------------------------------------------------------------------------------

--            Code n → ⟨ Stack Expr ⟩ n ↝ 1
code→expr⊙ : Code n → Stack Expr n → Expr
code→expr⊙ HALT        = snd
code→expr⊙ (PUSH v is) = code→expr⊙ is ∘ push [ v ]
code→expr⊙ (ADD    is) = code→expr⊙ is ∘ add

code→expr : Code zero → Expr
code→expr ds = code→expr⊙ ds tt

--------------------------------------------------------------------------------
-- Conversion from a Expr to a Code (compilation)
--------------------------------------------------------------------------------

expr→code⊙ : Expr → ⟨ Code ⟩ 1 ↝ 0
expr→code⊙ [ x ]     = PUSH x
expr→code⊙ (xs ⊕ ys) = expr→code⊙ xs ∘ expr→code⊙ ys ∘ ADD

expr→code : Expr → Code 0
expr→code tr = expr→code⊙ tr HALT

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

expr→code→expr⊙ : {is : Code (1 + n)} {st : Stack Expr n} (e : Expr) →
  code→expr⊙ (expr→code⊙ e is) st ≡ code→expr⊙ is (st ∷ e)
expr→code→expr⊙ [ x ]     = refl
expr→code→expr⊙ (xs ⊕ ys) = expr→code→expr⊙ xs ; expr→code→expr⊙ ys

code→expr→code⊙ : {st : Stack Expr n} (is : Code n) →
 expr→code (code→expr⊙ is st) ≡ foldl Code expr→code⊙ st is
code→expr→code⊙  HALT       = refl
code→expr→code⊙ (PUSH i is) = code→expr→code⊙ is
code→expr→code⊙ (ADD    is) = code→expr→code⊙ is

prog-iso : Code 0 ⇔ Expr
prog-iso .fun = code→expr
prog-iso .inv = expr→code
prog-iso .rightInv = expr→code→expr⊙
prog-iso .leftInv  = code→expr→code⊙
