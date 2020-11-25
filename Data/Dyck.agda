{-# OPTIONS --cubical --safe --postfix-projections #-}

-- This module defines a data type for balanced strings of parentheses,
-- which is isomorphic to binary trees.

module Data.Dyck where

open import Prelude
open import Data.List using (List)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Function.Surjective
open import Function.Injective
open import Data.Nat.Properties using (+-idʳ)
open import Data.Vec.Iterated

private
  variable
    n m k : ℕ

--------------------------------------------------------------------------------
-- Dyck words: definition and associated functions.
--------------------------------------------------------------------------------

-- A suffix of a Dyck word.
-- The type Dyck n represents a string
-- of pairs of parentheses, and n extra closing parens.
infixr 5 ⟨_ ⟩_
data Dyck : ℕ → Type₀ where
  done : Dyck zero
  ⟨_ : Dyck (suc n) → Dyck n
  ⟩_ : Dyck n → Dyck (suc n)

-- Some examples
_ : Dyck 0
_ = ⟨ ⟩ ⟨ ⟩ ⟨ ⟩ done

_ : Dyck 1
_ = ⟩ ⟨ ⟩ ⟨ ⟩ done

-- A helper function to list all the dyck
-- words of a given size. (handy for i.e. testing)
support-dyck : ∀ (n m : ℕ) → List (Dyck n)
support-dyck = λ n m → sup-k n m id []
  module ListDyck where
  open import Data.List using (_∷_; [])

  Diff : Type₀ → Type₁
  Diff A = ∀ {B : Type₀} → (A → B) → List B → List B

  mutual
    sup-k : (n m : ℕ) → Diff (Dyck n)
    sup-k n m k = end n m k ∘ lefts n m k ∘ rights n m k

    lefts : (n m : ℕ) → Diff (Dyck n)
    lefts n zero    k = id
    lefts n (suc m) k = sup-k (suc n) m (k ∘ ⟨_)

    rights : (n m : ℕ) → Diff (Dyck n)
    rights (suc n) m k = sup-k n m (k ∘ ⟩_)
    rights zero    m k = id

    end : (n m : ℕ) → Diff (Dyck n)
    end (suc _) _    k = id
    end zero (suc _) k = id
    end zero zero    k xs = k done ∷ xs

module _ {p} (P : ℕ → Type p)
             (lbrack : ∀ {n} → P (suc n) → P n)
             (rbrack : ∀ {n} → P n → P (suc n))
             (base : P 0)
             where
  foldrDyck : Dyck n → P n
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

--------------------------------------------------------------------------------
-- Conversion between binary trees and Dyck words.
--------------------------------------------------------------------------------

tree→dyck⊙ : (t : Tree) → Dyck n → Dyck n
tree→dyck⊙ leaf      d = d
tree→dyck⊙ (xs * ys) d = ⟨ tree→dyck⊙ xs (⟩ tree→dyck⊙ ys d)

-- Tree to Dyck
tree→dyck : (t : Tree) → Dyck zero
tree→dyck t = tree→dyck⊙ t done

reduce : Vec Tree (suc (suc n)) → Vec Tree (suc n)
reduce (x ∷ y ∷ xs) = (x * y) ∷ xs

shift : Vec Tree n → Vec Tree (suc n)
shift = leaf ∷_

dyck→tree⊙ : Vec Tree (suc k) → Dyck n → Vec Tree (suc n + k)
dyck→tree⊙ xs = foldrDyck (λ n → Vec Tree (suc n + _)) reduce shift xs

-- Dyck to tree
dyck→tree : Dyck zero → Tree
dyck→tree = head ∘ dyck→tree⊙ (leaf ∷ [])

dyck→treeˡ : Dyck zero → Tree
dyck→treeˡ d = go d (leaf ∷ [])
  where
  go : Dyck n → Vec Tree (suc n) → Tree
  go (⟨ d)  ts              = go d (leaf    ∷ ts)
  go (⟩ d)  (t₁ ∷ t₂ ∷ ts)  = go d (t₂ * t₁ ∷ ts)
  go done   (t  ∷ _)         = t

dyck→tree→dyck-pop : ∀ (xs : Vec Tree (suc k)) (d : Dyck n) t → dyck→tree⊙ xs (tree→dyck⊙ t (⟩ d)) ≡ t ∷ dyck→tree⊙ xs d
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

s : Dyck 0 ↠! Tree
s .fst = dyck→tree
s .snd y .fst = tree→dyck y
s .snd y .snd = dyck→tree→dyck y

unpack : Vec Tree (suc n) → Vec Tree (suc (suc n))
unpack (leaf ∷ xs) = leaf ∷ leaf ∷ xs
unpack ((x * x₁) ∷ xs) = x ∷ x₁ ∷ xs

reduce-inj : (xs ys : Vec Tree (suc (suc n))) → reduce xs ≡ reduce ys → xs ≡ ys
reduce-inj (head₁ ∷ head₃ ∷ tail₁) (head₂ ∷ head₄ ∷ tail₂) xs≡ys = cong unpack xs≡ys

import Data.Nat.Properties as ℕ


size⊙ : Tree → ℕ → ℕ
size⊙ leaf n = n
size⊙ (xs * ys) n = suc (size⊙ xs (size⊙ ys n))

sizes⊙ : Vec Tree n → ℕ → ℕ
sizes⊙ xs n = foldr′ size⊙ n xs

lefts⊙ : Dyck n → ℕ → ℕ
lefts⊙ done n = n
lefts⊙ (⟨ d) n = suc (lefts⊙ d n)
lefts⊙ (⟩ d) n = lefts⊙ d n

sizes : Vec Tree n → ℕ
sizes xs = sizes⊙ xs 0

not-branch-leaf : ∀ {xs ys} → xs * ys ≢ leaf
not-branch-leaf = ℕ.snotz ∘ cong (flip size⊙ 0)

reduce≢shift : (xs : Vec Tree (suc (suc n))) → (ys : Vec Tree n) → reduce xs ≢ shift ys
reduce≢shift (x₁ ∷ x₂ ∷ xs) ys xs≡ys = not-branch-leaf (cong head xs≡ys)

sizes-reduce : ∀ (xs : Vec Tree (suc (suc k))) → sizes⊙ (reduce xs) m ≡ suc (sizes⊙ xs m)
sizes-reduce (x₁ ∷ x₂ ∷ xs) = refl

lemma₂ : (vs : Vec Tree (suc k)) → (xs : Dyck n) → ∀ m → sizes⊙ (dyck→tree⊙ vs xs) m ≡ lefts⊙ xs (sizes⊙ vs m)
lemma₂ vs done   _ = refl
lemma₂ vs (⟨ xs) m = sizes-reduce (dyck→tree⊙ vs xs) ; cong suc (lemma₂ vs xs m)
lemma₂ vs (⟩ xs) m = lemma₂ vs xs m


suc-distrib-lefts : ∀ n (x : Dyck m) → suc (lefts⊙ x n) ≡ lefts⊙ x (suc n)
suc-distrib-lefts n done = refl
suc-distrib-lefts n (⟨ x) = cong suc (suc-distrib-lefts n x)
suc-distrib-lefts n (⟩ x) = suc-distrib-lefts n x

lefts-inj : ∀ n (x : Dyck m) → n ≢ suc (lefts⊙ x n)
lefts-inj zero x p = ℕ.znots p
lefts-inj (suc n) x p = lefts-inj n x (cong ℕ.pred p ; sym (suc-distrib-lefts n x))

dyck→tree⊙-inj : (vs : Vec Tree (suc k)) → (xs ys : Dyck n) → dyck→tree⊙ vs xs ≡ dyck→tree⊙ vs ys → xs ≡ ys
dyck→tree⊙-inj vs done done xs≡ys = refl
dyck→tree⊙-inj vs done (⟨ ys) xs≡ys = let p = sym (lemma₂ vs done 0) ; cong sizes xs≡ys ; lemma₂ vs (⟨ ys) 0 in ⊥-elim (lefts-inj (sizes⊙ vs 0) ys p)
dyck→tree⊙-inj vs (⟨ xs) done xs≡ys = let p = sym (lemma₂ vs done 0) ; cong sizes (sym xs≡ys) ; lemma₂ vs (⟨ xs) 0 in ⊥-elim (lefts-inj (sizes⊙ vs 0) xs p)
dyck→tree⊙-inj vs (⟨ xs) (⟨ ys) xs≡ys = cong ⟨_ (dyck→tree⊙-inj vs xs ys (reduce-inj (dyck→tree⊙ vs xs) (dyck→tree⊙ vs ys) xs≡ys))
dyck→tree⊙-inj vs (⟨ xs) (⟩ ys) xs≡ys = ⊥-elim (reduce≢shift (dyck→tree⊙ vs xs) (dyck→tree⊙ vs ys) xs≡ys)
dyck→tree⊙-inj vs (⟩ xs) (⟨ ys) xs≡ys = ⊥-elim (reduce≢shift (dyck→tree⊙ vs ys) (dyck→tree⊙ vs xs) (sym xs≡ys))
dyck→tree⊙-inj vs (⟩ xs) (⟩ ys) xs≡ys = cong ⟩_ (dyck→tree⊙-inj vs xs ys (cong tail xs≡ys))

lemma : (xs ys : Vec A 1) → head xs ≡ head ys → xs ≡ ys
lemma (head₁ ∷ []) (head₂ ∷ []) p = cong (_∷ []) p

dyck→tree-inj : (xs ys : Dyck 0) → dyck→tree xs ≡ dyck→tree ys → xs ≡ ys
dyck→tree-inj xs ys xs≡ys = dyck→tree⊙-inj (leaf ∷ []) xs ys (lemma (dyck→tree⊙ (leaf ∷ []) xs) (dyck→tree⊙ (leaf ∷ []) ys) xs≡ys)

dyck⇔tree : Dyck 0 ⇔ Tree
dyck⇔tree = surj×inj⇒iso dyck→tree (λ y → tree→dyck y , dyck→tree→dyck y) dyck→tree-inj
