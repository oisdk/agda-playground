{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck where

open import Prelude
open import Data.Vec
open import Data.List
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Function.Surjective

private
  variable
    n m k : ℕ

--------------------------------------------------------------------------------
-- Dyck words: definition and associated functions.
--------------------------------------------------------------------------------

-- A Prefix of a Dyck word.
-- The type Dyck n m represents a string
-- of m pairs of parentheses, and n extra closing parens.
infixr 5 ⟨_ ⟩_
data Dyck : ℕ → ℕ → Type₀ where
  done : Dyck zero zero
  ⟨_ : Dyck (suc n) m → Dyck n (suc m)
  ⟩_ : Dyck n m → Dyck (suc n) m

-- A string of balanced parentheses
Bal : Type₀
Bal = ∃[ n ] Dyck zero n

-- Some examples
_ : Dyck 0 3
_ = ⟨ ⟩ ⟨ ⟩ ⟨ ⟩ done

_ : Dyck 1 2
_ = ⟩ ⟨ ⟩ ⟨ ⟩ done

-- A helper function to list all the dyck
-- words of a given size. (handy for i.e. testing)
support-dyck : ∀ n m → List (Dyck n m)
support-dyck = λ n m → sup-k n m id []
  module ListDyck where
  Diff : Type₀ → Type₁
  Diff A = ∀ {B : Type₀} → (A → B) → List B → List B

  mutual
    sup-k : ∀ n m → Diff (Dyck n m)
    sup-k n m k = end n m k ∘ lefts n m k ∘ rights n m k

    lefts : ∀ n m → Diff (Dyck n m)
    lefts n zero    k = id
    lefts n (suc m) k = sup-k (suc n) m (k ∘ ⟨_)

    rights : ∀ n m → Diff (Dyck n m)
    rights (suc n) m k = sup-k n m (k ∘ ⟩_)
    rights zero    m k = id

    end : ∀ n m → Diff (Dyck n m)
    end (suc _) _    k = id
    end zero (suc _) k = id
    end zero zero    k xs = k done ∷ xs

module _ {p} (P : ℕ → ℕ → Type p)
             (lbrack : ∀ {n m} → P (suc n) m → P n (suc m))
             (rbrack : ∀ {n m} → P n m → P (suc n) m)
             (base : P 0 0)
             where
  foldrDyck : Dyck n m → P n m
  foldrDyck done = base
  foldrDyck (⟨ x) = lbrack (foldrDyck x)
  foldrDyck (⟩ x) = rbrack (foldrDyck x)

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions.
--------------------------------------------------------------------------------

-- A basic binary tree type.
data Tree : Type₀ where
  leaf : Tree
  _*_  : Tree → Tree → Tree

-- This pair of functions gives the number of internal nodes
-- in the tree.
--
-- Note: we use the symbol ⊙ for helper functions which return
-- the endo monoid for the function itself.
size⊙ : Tree → ℕ → ℕ
size⊙ leaf      n = n
size⊙ (xs * ys) n = suc (size⊙ xs (size⊙ ys n))

size : Tree → ℕ
size t = size⊙ t 0

--------------------------------------------------------------------------------
-- Conversion between binary trees and Dyck words.
--------------------------------------------------------------------------------

tree→dyck⊙ : (t : Tree) → Dyck n m → Dyck n (size⊙ t m)
tree→dyck⊙ leaf      d = d
tree→dyck⊙ (xs * ys) d = ⟨ tree→dyck⊙ xs (⟩ tree→dyck⊙ ys d)

-- Tree to Dyck
tree→dyck : (t : Tree) → Dyck zero (size t)
tree→dyck t = tree→dyck⊙ t done

reduce : Vec Tree (suc (suc n)) → Vec Tree (suc n)
reduce (x ∷ y ∷ xs) = (x * y) ∷ xs

shift : Vec Tree n → Vec Tree (suc n)
shift xs = leaf ∷ xs

dyck→tree⊙ : Vec Tree (suc k) → Dyck n m → Vec Tree (suc n + k)
dyck→tree⊙ xs = foldrDyck (λ n m → Vec Tree (suc n + _)) reduce shift xs

-- Dyck to tree
dyck→tree : Dyck zero n → Tree
dyck→tree = head ∘ dyck→tree⊙ (leaf ∷ [])

dyck→tree→dyck-pop : ∀ (xs : Vec Tree (suc k)) (d : Dyck n m) t → dyck→tree⊙ xs (tree→dyck⊙ t (⟩ d)) ≡ (t ∷ dyck→tree⊙ xs d)
dyck→tree→dyck-pop xs d leaf = refl
dyck→tree→dyck-pop xs d (ls * rs) =
  dyck→tree⊙ xs (⟨ tree→dyck⊙ ls (⟩ tree→dyck⊙ rs (⟩ d)))        ≡⟨⟩
  reduce (dyck→tree⊙ xs (tree→dyck⊙ ls (⟩ tree→dyck⊙ rs (⟩ d)))) ≡⟨ cong reduce (dyck→tree→dyck-pop xs (tree→dyck⊙ rs (⟩ d)) ls) ⟩
  reduce (ls ∷ dyck→tree⊙ xs (tree→dyck⊙ rs (⟩ d)))              ≡⟨ cong reduce (cong (ls ∷_) (dyck→tree→dyck-pop xs d rs)) ⟩
  reduce (ls ∷ rs ∷ dyck→tree⊙ xs d)                             ≡⟨⟩
  (ls * rs) ∷ dyck→tree⊙ xs d ∎

dyck→tree→dyck-push : ∀ t (xs : Vec Tree n) → dyck→tree⊙ (leaf ∷ xs) (tree→dyck t) ≡ t ∷ xs
dyck→tree→dyck-push leaf      xs = refl
dyck→tree→dyck-push (ls * rs) xs =
  dyck→tree⊙ (leaf ∷ xs) (tree→dyck (ls * rs))                     ≡⟨⟩
  reduce (dyck→tree⊙ (leaf ∷ xs) (tree→dyck⊙ ls (⟩ tree→dyck rs))) ≡⟨ cong reduce (dyck→tree→dyck-pop (leaf ∷ xs) (tree→dyck rs) ls ) ⟩
  reduce (ls ∷ dyck→tree⊙ (leaf ∷ xs) (tree→dyck rs))              ≡⟨ cong reduce (cong (ls ∷_) (dyck→tree→dyck-push rs xs)) ⟩
  (ls * rs) ∷ xs ∎

dyck→tree→dyck : ∀ t → dyck→tree (tree→dyck t) ≡ t
dyck→tree→dyck t = cong head (dyck→tree→dyck-push t [])

-- Proof that conversion from dyck to tree is surjective
dyck↠tree : Bal ↠! Tree
dyck↠tree .fst (_ , x) = dyck→tree x
dyck↠tree .snd y .fst = _ , tree→dyck y
dyck↠tree .snd y .snd = dyck→tree→dyck y

sizes : Vec Tree n → ℕ
sizes = Data.Vec.foldr size⊙ zero

reduce-suc : (xs : Vec Tree (2 + n)) → sizes (reduce xs) ≡ suc (sizes xs)
reduce-suc (_ ∷ _ ∷ _) = refl

size-rev⊙ : (d : Dyck n m) → (v : Vec Tree (suc k)) → m + sizes v ≡ sizes (dyck→tree⊙ v d)
size-rev⊙ done  v = refl
size-rev⊙ {n = n} {m = suc m} (⟨ d) v =
  suc (m + sizes v) ≡⟨ cong suc (size-rev⊙ d v) ⟩
  suc (sizes (dyck→tree⊙ v d)) ≡˘⟨ reduce-suc (dyck→tree⊙ v d) ⟩
  sizes (reduce (dyck→tree⊙ v d)) ≡⟨⟩
  sizes (dyck→tree⊙ v (⟨ d)) ∎
size-rev⊙ {m = m} (⟩ d) v = size-rev⊙ d v

size⊙-head : (v : Vec Tree 1) →  size (head v) ≡ sizes v
size⊙-head (x ∷ []) = refl

import Data.Nat.Properties as ℕ

size-rev : (d : Dyck zero n) → size (dyck→tree d) ≡ n
size-rev {n = n} d =
  size (dyck→tree d) ≡⟨⟩
  size (head (dyck→tree⊙ (leaf ∷ []) d)) ≡⟨⟩
  size (head (dyck→tree⊙ (leaf ∷ []) d)) ≡⟨ size⊙-head  (dyck→tree⊙ (leaf ∷ []) d) ⟩
  sizes (dyck→tree⊙ (leaf ∷ []) d) ≡˘⟨ size-rev⊙ d (leaf ∷ []) ⟩
  n + 0 ≡⟨ ℕ.+-idʳ n ⟩
  n ∎
