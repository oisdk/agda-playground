{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck.Payload where

open import Prelude
open import Data.List using (List)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Function.Surjective
open import Function.Injective
open import Data.Nat.Properties using (snotz; znots; pred)
open import Data.Vec.Iterated

private
  variable
    n m k : ℕ

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions.
--------------------------------------------------------------------------------

-- A basic binary tree type.
data Tree (A : Type a) : Type a where
  [_] : A → Tree A
  _*_ : Tree A → Tree A → Tree A

-- Counts the number of branches in the tree
size⊙ : Tree A → ℕ → ℕ
size⊙ [ _ ]     = id
size⊙ (xs * ys) = suc ∘ size⊙ xs ∘ size⊙ ys

size : Tree A → ℕ
size t = size⊙ t zero

--------------------------------------------------------------------------------
-- Conversion between binary trees and Progs. (leftwards)
--------------------------------------------------------------------------------

data Prog {a} (A : Type a) : ℕ → Type a where
  halt : Prog A zero
  push : A → Prog A (suc n) → Prog A n
  pull : Prog A n → Prog A (suc n)

foldlProg : ∀ {p} (P : ℕ → Type p)
            (lbrack : ∀ {n} → P (suc n) → P n)
            (rbrack : ∀ {n} → A → P n → P (suc n))
            (base : P n) →
            Prog A n → P zero
foldlProg P lb rb bs halt = bs
foldlProg P lb rb bs (push x xs) = foldlProg P lb rb (rb x bs) xs
foldlProg P lb rb bs (pull   xs) = foldlProg P lb rb (lb bs) xs
-- In terms of foldr:
-- foldlProg P lb rb bs xs = foldrProg (λ n → P n → P zero) (λ x k bs → k (rb x bs)) (λ k bs → k (lb bs)) id xs bs

reduce : Vec (Tree A) (2 + n) → Vec (Tree A) (1 + n)
reduce (t₁ ∷ t₂ ∷ s) = (t₂ * t₁) ∷ s

shift : A → Vec (Tree A) n → Vec (Tree A) (1 + n)
shift x s = [ x ] ∷ s

prog→tree⊙ : Prog A n → Vec (Tree A) (1 + n) → Vec (Tree A) 1
prog→tree⊙ p s = foldlProg (λ n → Vec (Tree _) (1 + n)) reduce shift s p

-- prog→tree⊙ halt                   s  = s
-- prog→tree⊙ (push x ds)            s  = prog→tree⊙ ds ([ x ] ∷ s)
-- prog→tree⊙ (pull   ds) (t₁ ∷ t₂ ∷ s) = prog→tree⊙ ds ((t₂ * t₁) ∷ s)

prog→tree : A × Prog A zero → Tree A
prog→tree (x , ds) = head (prog→tree⊙ ds ([ x ] ∷ []))

tree→prog⊙ : Tree A → Prog A n → A × Prog A n
tree→prog⊙ [ x ]     = x ,_
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ uncurry push ∘ tree→prog⊙ ys ∘ pull

tree→prog : Tree A → A × Prog A zero
tree→prog tr = tree→prog⊙ tr halt

shuttle : A × Prog A n → Vec (Tree A) m → Prog A n × Vec (Tree A) (suc m)
shuttle (x , xs) ys = xs , [ x ] ∷ ys

-- tree→prog→tree⊙ : ∀ (e : Tree A) (is : Prog A n) (st : Vec (Tree A) n) → uncurry prog→tree⊙ (shuttle (tree→prog⊙ e is) st) ≡ prog→tree⊙ is (e ∷ st)
-- tree→prog→tree⊙ [ x ]     is st = refl
-- tree→prog→tree⊙ (xs * ys) is st =
--   uncurry prog→tree⊙ (shuttle (tree→prog⊙ xs (uncurry push (tree→prog⊙ ys (pull is)))) st) ≡⟨ tree→prog→tree⊙ xs _ st ⟩
--   prog→tree⊙  (uncurry push (tree→prog⊙ ys (pull is))) (xs ∷ st) ≡⟨ {!!} ⟩
--   prog→tree⊙ is ((xs * ys) ∷ st) ∎

-- tree→prog→tree : (t : Tree A) → prog→tree (tree→prog t) ≡ t
-- tree→prog→tree t = {!!}

-- prog→tree→prog : (x : A × Prog A zero) → tree→prog (prog→tree x) ≡ x
-- prog→tree→prog = {!!}
