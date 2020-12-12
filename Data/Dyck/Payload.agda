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
  halt : Prog A 1
  push : A → Prog A (1 + n) → Prog A n
  pull : Prog A (1 + n) → Prog A (2 + n)

module _{p} (P : ℕ → Type p)
             (lbrack : ∀ {n} → P (2 + n) → P (1 + n))
             (rbrack : ∀ {n} → A → P n → P (1 + n))
             where
  foldlProg : P n → Prog A n → P 1
  foldlProg bs halt = bs
  foldlProg bs (push x xs) = foldlProg (rbrack x bs) xs
  foldlProg bs (pull   xs) = foldlProg (lbrack bs) xs
-- In terms of foldr:
-- foldlProg P lb rb bs xs = foldrProg (λ n → P n → P zero) (λ x k bs → k (rb x bs)) (λ k bs → k (lb bs)) id xs bs

reduce : Vec (Tree A) (2 + n) → Vec (Tree A) (1 + n)
reduce (t₁ ∷ t₂ ∷ s) = (t₂ * t₁) ∷ s

shift : A → Vec (Tree A) n → Vec (Tree A) (1 + n)
shift x s = [ x ] ∷ s

prog→tree⊙ : Prog A n → Vec (Tree A) ( n) → Vec (Tree A) 1
prog→tree⊙ p s = foldlProg (λ n → Vec (Tree _) ( n)) reduce shift s p

prog→tree : Prog A zero → Tree A
prog→tree ds = head (prog→tree⊙ ds [])

tree→prog⊙ : Tree A → Prog A (suc n) → Prog A n
tree→prog⊙ [ x ]     = push x
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ tree→prog⊙ ys ∘ pull

tree→prog : Tree A → Prog A zero
tree→prog tr = tree→prog⊙ tr halt

tree→prog→tree-assoc : (xs : Tree A) (is : Prog A (1 + n)) (st : Vec (Tree A) n) → prog→tree⊙ (tree→prog⊙ xs is) st ≡ prog→tree⊙ is (xs ∷ st)
tree→prog→tree-assoc [ x ]     is st = refl
tree→prog→tree-assoc (xs * ys) is st = tree→prog→tree-assoc xs _ st ; tree→prog→tree-assoc ys (pull is) (xs ∷ st)

tree→prog→tree-ε : (e : Tree A) (is : Prog A (1 + n)) (st : Vec (Tree A) n) → prog→tree⊙ (tree→prog⊙ e is) st ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree-ε [ x ]     is st = refl
tree→prog→tree-ε (xs * ys) is st = tree→prog→tree-ε xs _ st ; tree→prog→tree-assoc ys (pull is) (xs ∷ st)

tree→prog→tree : (t : Tree A) → prog→tree (tree→prog t) ≡ t
tree→prog→tree t = cong head (tree→prog→tree-ε t halt [])

push-inj : ∀ {x y : A} (xs ys : Prog A (suc n)) → push x xs ≡ push y ys → xs ≡ ys
push-inj xs ys = cong (λ { halt → ys ; (push x pr) → pr ; (pull pr) → ys})

pull-inj : ∀ (xs ys : Prog A (suc n)) → pull xs ≡ pull ys → xs ≡ ys
pull-inj xs ys = cong (λ { (push x pr) → ys ; (pull pr) → pr})

tree→prog⊙-inj : (ts : Tree A) → Injective (tree→prog⊙ {n = n} ts)
tree→prog⊙-inj [ v ] x y = push-inj _ _
tree→prog⊙-inj (ts₁ * ts₂) x y f⟨x⟩≡f⟨y⟩ =
  let p = tree→prog⊙-inj ts₁ (tree→prog⊙ ts₂ (pull x)) (tree→prog⊙ ts₂ (pull y)) f⟨x⟩≡f⟨y⟩
      q = tree→prog⊙-inj ts₂ (pull x) (pull y) p
  in pull-inj _ _ q

trees→prog⊙ : Vec (Tree A) n → Prog A n → Prog A 0
trees→prog⊙ vs xs = foldlN (Prog _) tree→prog⊙ xs vs

trees→prog-one : Vec (Tree A) 1 → Prog A zero
trees→prog-one xs = tree→prog⊙ (head xs) halt

trees→prog⊙-inj : {A : Type a} (vs : Vec (Tree A) n) → Injective (trees→prog⊙ vs)
trees→prog⊙-inj {n = zero}       vs  x y f⟨x⟩≡f⟨y⟩ = f⟨x⟩≡f⟨y⟩
trees→prog⊙-inj {n = suc n} (v ∷ vs) x y f⟨x⟩≡f⟨y⟩ = tree→prog⊙-inj v x y (trees→prog⊙-inj vs (tree→prog⊙ v x) (tree→prog⊙ v y) f⟨x⟩≡f⟨y⟩)

conv : {A : Type a} (vs : Vec (Tree A) n) (xs : Prog A n) → tree→prog (head (prog→tree⊙ xs vs)) ≡ trees→prog⊙ vs xs
conv vs  halt       = refl
conv vs (push x xs) = conv (shift x vs) xs
conv vs (pull   xs) = conv (reduce  vs) xs

prog→tree⊙-inj : (vs : Vec (Tree A) n) (xs ys : Prog A n) → prog→tree⊙ xs vs ≡ prog→tree⊙ ys vs → xs ≡ ys
prog→tree⊙-inj vs xs ys prf = trees→prog⊙-inj vs xs ys (sym (conv vs xs) ; cong trees→prog-one prf ; conv vs ys)

prog→tree-inj : Injective (prog→tree {A = A})
prog→tree-inj xs ys fx≡fy = prog→tree⊙-inj [] xs ys (cong (_∷ []) fx≡fy)

prog-iso : Prog A zero ⇔ Tree A
prog-iso = surj×inj⇒iso prog→tree (λ y → tree→prog y , tree→prog→tree y) prog→tree-inj
