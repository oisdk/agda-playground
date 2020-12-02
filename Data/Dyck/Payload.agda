{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck.Payload where

open import Prelude
open import Data.List using (List; _∷_; [])
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

--------------------------------------------------------------------------------
-- Conversion between binary trees and Progs. (leftwards)
--------------------------------------------------------------------------------

data Prog {a} (A : Type a) : ℕ → Type a where
  halt : Prog A zero
  push : A → Prog A (suc n) → Prog A n
  pull : Prog A n → Prog A (suc n)

module _{p} (P : ℕ → Type p)
             (lbrack : ∀ {n} → P (suc n) → P n)
             (rbrack : ∀ {n} → A → P n → P (suc n))
             where
  foldlProg : P n → Prog A n → P zero
  foldlProg bs halt = bs
  foldlProg bs (push x xs) = foldlProg (rbrack x bs) xs
  foldlProg bs (pull   xs) = foldlProg (lbrack bs) xs
-- In terms of foldr:
-- foldlProg P lb rb bs xs = foldrProg (λ n → P n → P zero) (λ x k bs → k (rb x bs)) (λ k bs → k (lb bs)) id xs bs

  -- module _ (linj : ∀ {n} {xs ys : P (suc n)} → lbrack xs ≡ lbrack ys → xs ≡ ys)
  --          (rinj : ∀ {n} {x y : A} {xs ys : P n} → rbrack x xs ≡ rbrack y ys → (x , xs) ≡ (y , ys)) where

  --   foldl-inj′ : (bs₁ bs₂ : P n) (is₁ is₂ : Prog A n) → foldlProg bs₁ is₁ ≡ foldlProg bs₂ is₂ → bs₁ ≡ bs₂
  --   foldl-inj′ bs₁ bs₂ halt halt fxs≡fys = fxs≡fys
  --   foldl-inj′ bs₁ bs₂ (pull xs) (pull ys) fxs≡fys = linj (foldl-inj′ (lbrack bs₁) (lbrack bs₂) xs ys fxs≡fys)
  --   foldl-inj′ bs₁ bs₂ (push x xs) (push y ys) fxs≡fys = cong snd (rinj (foldl-inj′ (rbrack x bs₁) (rbrack y bs₂) xs ys fxs≡fys))
  --   foldl-inj′ bs₁ bs₂ halt (push x ys) fxs≡fys = {!!}
  --   foldl-inj′ bs₁ bs₂ (push x xs) halt fxs≡fys = {!!}
  --   foldl-inj′ bs₁ bs₂ (push x xs) (pull ys) fxs≡fys = {!!}
  --   foldl-inj′ bs₁ bs₂ (pull xs) (push x ys) fxs≡fys = {!!}

  --   foldl-inj : (bs₁ bs₂ : P n) (is₁ is₂ : Prog A n) → foldlProg bs₁ is₁ ≡ foldlProg bs₂ is₂ → is₁ ≡ is₂
  --   foldl-inj bs₁ bs₂ halt halt fxs≡fys = refl
  --   foldl-inj bs₁ bs₂ (pull xs) (pull ys) fxs≡fys = cong pull (foldl-inj (lbrack bs₁) (lbrack bs₂)  xs ys fxs≡fys)
  --   foldl-inj bs₁ bs₂ (push x xs) (push y ys) fxs≡fys = cong₂ push (cong fst (rinj (foldl-inj′ (rbrack x bs₁) (rbrack y bs₂) xs ys fxs≡fys))) (foldl-inj (rbrack x bs₁) (rbrack y bs₂) xs ys fxs≡fys)
  --   foldl-inj bs₁ bs₂ halt (push x ys) fxs≡fys = {!!}
  --   foldl-inj bs₁ bs₂ (push x xs) halt fxs≡fys = {!!}
  --   foldl-inj bs₁ bs₂ (push x xs) (pull ys) fxs≡fys = {!!}
  --   foldl-inj bs₁ bs₂ (pull xs) (push x ys) fxs≡fys = {!!}

reduce : Vec (Tree A) (2 + n) → Vec (Tree A) (1 + n)
reduce (t₁ ∷ t₂ ∷ s) = (t₂ * t₁) ∷ s

shift : A → Vec (Tree A) n → Vec (Tree A) (1 + n)
shift x s = [ x ] ∷ s

prog→tree⊙ : Prog A n → Vec (Tree A) (1 + n) → Vec (Tree A) 1
prog→tree⊙ p s = foldlProg (λ n → Vec (Tree _) (1 + n)) reduce shift s p

prog→tree : A × Prog A zero → Tree A
prog→tree (x , ds) = head (prog→tree⊙ ds ([ x ] ∷ []))

tree→prog⊙ : Tree A → Prog A n → A × Prog A n
tree→prog⊙ [ x ]     = x ,_
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ uncurry push ∘ tree→prog⊙ ys ∘ pull

tree→prog : Tree A → A × Prog A zero
tree→prog tr = tree→prog⊙ tr halt

shuttle : A × Prog A n → Vec (Tree A) m → Prog A n × Vec (Tree A) (suc m)
shuttle (x , xs) ys = xs , [ x ] ∷ ys

tree→prog→tree-assoc : (xs : Tree A) (is : Prog A (1 + n)) (st : Vec (Tree A) (1 + n)) → prog→tree⊙ (uncurry push (tree→prog⊙ xs is)) st ≡ prog→tree⊙ is (xs ∷ st)
tree→prog→tree-assoc [ x ]     is st = refl
tree→prog→tree-assoc (xs * ys) is st = tree→prog→tree-assoc xs _ st ; tree→prog→tree-assoc ys (pull is) (xs ∷ st)

tree→prog→tree-ε : (e : Tree A) (is : Prog A n) (st : Vec (Tree A) n) → uncurry prog→tree⊙ (shuttle (tree→prog⊙ e is) st) ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree-ε [ x ]     is st = refl
tree→prog→tree-ε (xs * ys) is st =
  uncurry prog→tree⊙ (shuttle (tree→prog⊙ xs (uncurry push (tree→prog⊙ ys (pull is)))) st) ≡⟨ tree→prog→tree-ε xs _ st ⟩
  prog→tree⊙  (uncurry push (tree→prog⊙ ys (pull is))) (xs ∷ st) ≡⟨ tree→prog→tree-assoc ys (pull is) (xs ∷ st) ⟩
  prog→tree⊙ is ((xs * ys) ∷ st) ∎

tree→prog→tree : (t : Tree A) → prog→tree (tree→prog t) ≡ t
tree→prog→tree t = cong head (tree→prog→tree-ε t halt [])

unreduce : Vec (Tree A) (1 + n) → Vec (Tree A) (2 + n)
unreduce ([ x ] ∷ xs) = [ x ] ∷ [ x ] ∷ xs
unreduce ((x₁ * x₂) ∷ xs) = x₂ ∷ x₁ ∷ xs

reduce-inj : {xs ys : Vec (Tree A) (2 + n)} → reduce xs ≡ reduce ys → xs ≡ ys
reduce-inj xs≡ys = cong unreduce xs≡ys

root : Tree A → A
root [ x ] = x
root (xs * _) = root xs

shift-inj : ∀ {A : Type a} {x y : A} {xs ys : Vec (Tree A) n} → shift x xs ≡ shift y ys → (x , xs) ≡ (y , ys)
shift-inj = cong λ where (z ∷ zs) → root z , zs

