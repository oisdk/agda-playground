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

encode⊙ : Tree A → List (Maybe A) → List (Maybe A)
encode⊙ [ x ] = just x ∷_
encode⊙ (xs * ys) = encode⊙ xs ∘ encode⊙ ys ∘ (nothing ∷_)

encodes⊙ : Vec (Tree A) n → List (Maybe A) → List (Maybe A)
encodes⊙ = flip (foldl′ encode⊙)

encodes : Vec (Tree A) n → List (Maybe A)
encodes xs = encodes⊙ xs []

open import Data.List.Properties using (∷-inj)

tail′ : List A → List A
tail′ (_ ∷ xs) = xs
tail′ [] = []

head′ : List (Maybe A) → Maybe A
head′ [] = nothing
head′ (x ∷ _) = x

encode⊙-inj : (ts : Tree A) → Injective (encode⊙ ts)
encode⊙-inj [ x ]       xs ys xs≡ys = ∷-inj (just x) xs ys xs≡ys
encode⊙-inj (ts₁ * ts₂) xs ys xs≡ys = cong tail′ (encode⊙-inj ts₂ (nothing ∷ xs) (nothing ∷ ys) (encode⊙-inj ts₁ (encode⊙ ts₂ (nothing ∷ xs)) (encode⊙ ts₂ (nothing ∷ ys)) xs≡ys))

encodes⊙-inj : {A : Type a} (vs : Vec (Tree A) n) → Injective (encodes⊙ vs)
encodes⊙-inj {n = zero } vs       xs ys fxs≡fys = fxs≡fys
encodes⊙-inj {n = suc n} (v ∷ vs) xs ys fxs≡fys = encode⊙-inj v xs ys (encodes⊙-inj vs (encode⊙ v xs) (encode⊙ v ys) fxs≡fys)

unind : Prog A n → List (Maybe A)
unind halt        = []
unind (push x xs) = just x  ∷ unind xs
unind (pull   xs) = nothing ∷ unind xs

unind-conv : {A : Type a} (vs : Vec (Tree A) n) (xs : Prog A n) → encodes (prog→tree⊙ xs vs) ≡ encodes⊙ vs (unind xs)
unind-conv vs  halt       = refl
unind-conv vs (push x xs) = unind-conv (shift x vs) xs
unind-conv vs (pull   xs) = unind-conv (reduce  vs) xs

prog→tree→unind→inj : (vs : Vec (Tree A) n) (xs ys : Prog A n) → prog→tree⊙ xs vs ≡ prog→tree⊙ ys vs → unind xs ≡ unind ys
prog→tree→unind→inj vs xs ys prf = encodes⊙-inj vs (unind xs) (unind ys) (sym (unind-conv vs xs) ; cong encodes prf ; unind-conv vs ys)

open import Data.Maybe.Properties

unind-inj : Injective (unind {A = A} {n = n})
unind-inj halt         halt       f⟨x⟩≡f⟨y⟩ = refl
unind-inj halt        (push y ys) f⟨x⟩≡f⟨y⟩ = ⊥-elim (znots (cong length f⟨x⟩≡f⟨y⟩))
unind-inj (push x xs)  halt       f⟨x⟩≡f⟨y⟩ = ⊥-elim (snotz (cong length f⟨x⟩≡f⟨y⟩))
unind-inj (push x xs) (push y ys) f⟨x⟩≡f⟨y⟩ = cong₂ push (cong (λ { nothing → y ; (just x) → x}) (cong head′ f⟨x⟩≡f⟨y⟩)) (unind-inj _ _ (cong tail′ f⟨x⟩≡f⟨y⟩))
unind-inj (push x xs) (pull   ys) f⟨x⟩≡f⟨y⟩ = ⊥-elim (just≢nothing (cong head′ f⟨x⟩≡f⟨y⟩))
unind-inj (pull   xs) (push y ys) f⟨x⟩≡f⟨y⟩ = ⊥-elim (nothing≢just (cong head′ f⟨x⟩≡f⟨y⟩))
unind-inj (pull   xs) (pull   ys) f⟨x⟩≡f⟨y⟩ = cong pull (unind-inj xs ys (cong tail′ f⟨x⟩≡f⟨y⟩))


prog→tree⊙-inj : (vs : Vec (Tree A) ( n)) → (xs ys : Prog A n) → prog→tree⊙ xs vs ≡ prog→tree⊙ ys vs → xs ≡ ys
prog→tree⊙-inj vs xs ys fxs≡fys = unind-inj xs ys (prog→tree→unind→inj vs xs ys fxs≡fys)

head-zero : (xs ys : Vec A 1) → head xs ≡ head ys → xs ≡ ys
head-zero (x ∷ []) (y ∷ []) prf = cong (_∷ []) prf

prog→tree-inj : Injective (prog→tree {A = A})
prog→tree-inj xs ys fx≡fy = prog→tree⊙-inj [] xs ys (head-zero _ _ fx≡fy)

prog-iso : Prog A zero ⇔ Tree A
prog-iso = surj×inj⇒iso prog→tree (λ y → tree→prog y , tree→prog→tree y) prog→tree-inj
