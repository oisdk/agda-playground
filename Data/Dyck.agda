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
open import Data.Nat.Properties using (snotz; znots; pred)
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

foldlDyck : ∀ {p} (P : ℕ → Type p)
            (lbrack : ∀ {n} → P (suc n) → P n)
            (rbrack : ∀ {n} → P n → P (suc n))
            (base : P n) →
            Dyck n → P zero
-- foldlDyck P lb rb bs xs = foldrDyck (λ n → P n → P zero) (λ k bs → k (rb bs)) (λ k bs → k (lb bs)) id xs bs
foldlDyck P lb rb bs done = bs
foldlDyck P lb rb bs (⟨ xs) = foldlDyck P lb rb (rb bs) xs
foldlDyck P lb rb bs (⟩ xs) = foldlDyck P lb rb (lb bs) xs

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions.
--------------------------------------------------------------------------------

-- A basic binary tree type.
data Tree : Type₀ where
  leaf : Tree
  _*_  : Tree → Tree → Tree

-- Counts the number of branches in the tree
size⊙ : Tree → ℕ → ℕ
size⊙ leaf      = id
size⊙ (xs * ys) = suc ∘ size⊙ xs ∘ size⊙ ys

size : Tree → ℕ
size t = size⊙ t zero

--------------------------------------------------------------------------------
-- Conversion between binary trees and Dyck words. (rightwards)
--------------------------------------------------------------------------------

module Right where
  tree→dyck⊙ : (t : Tree) → Dyck n → Dyck n
  tree→dyck⊙ leaf      d = d
  tree→dyck⊙ (xs * ys) d = ⟨ tree→dyck⊙ xs (⟩ tree→dyck⊙ ys d)

  -- Tree to Dyck
  tree→dyck : (t : Tree) → Dyck zero
  tree→dyck t = tree→dyck⊙ t done

  reduce : Vec Tree (2 + n) → Vec Tree (suc n)
  reduce (x ∷ y ∷ xs) = (x * y) ∷ xs

  shift : Vec Tree n → Vec Tree (suc n)
  shift = leaf ∷_

  dyck→tree⊙ : Vec Tree (suc k) → Dyck n → Vec Tree (suc n + k)
  dyck→tree⊙ xs = foldrDyck (λ n → Vec Tree (suc n + _)) reduce shift xs

  -- Dyck to tree
  dyck→tree : Dyck zero → Tree
  dyck→tree = head ∘ dyck→tree⊙ (leaf ∷ [])

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

  unreduce : Vec Tree (suc n) → Vec Tree (2 + n)
  unreduce (leaf ∷ xs) = leaf ∷ leaf ∷ xs
  unreduce ((x₁ * x₂) ∷ xs) = x₁ ∷ x₂ ∷ xs

  reduce-inj : {xs ys : Vec Tree (2 + n)} → reduce xs ≡ reduce ys → xs ≡ ys
  reduce-inj xs≡ys = cong unreduce xs≡ys


  sizes⊙ : Vec Tree n → ℕ → ℕ
  sizes⊙ xs n = foldr′ size⊙ n xs

  lefts⊙ : Dyck n → ℕ → ℕ
  lefts⊙ done n = n
  lefts⊙ (⟨ d) n = suc (lefts⊙ d n)
  lefts⊙ (⟩ d) n = lefts⊙ d n

  sizes : Vec Tree n → ℕ
  sizes xs = sizes⊙ xs 0

  reduce≢shift : {xs : Vec Tree (2 + n)} → {ys : Vec Tree n} → reduce xs ≢ shift ys
  reduce≢shift = snotz ∘ cong (size ∘ head)

  sizes-lefts : (vs : Vec Tree (suc k)) → (xs : Dyck n) → sizes⊙ (dyck→tree⊙ vs xs) m ≡ lefts⊙ xs (sizes⊙ vs m)
  sizes-lefts vs done   = refl
  sizes-lefts vs (⟨ xs) = cong suc (sizes-lefts vs xs)
  sizes-lefts vs (⟩ xs) = sizes-lefts vs xs

  suc-distrib-lefts : ∀ n (x : Dyck m) → suc (lefts⊙ x n) ≡ lefts⊙ x (suc n)
  suc-distrib-lefts n done = refl
  suc-distrib-lefts n (⟨ x) = cong suc (suc-distrib-lefts n x)
  suc-distrib-lefts n (⟩ x) = suc-distrib-lefts n x

  lefts-monot : ∀ n (x : Dyck m) → n ≢ suc (lefts⊙ x n)
  lefts-monot zero x p = znots p
  lefts-monot (suc n) x p = lefts-monot n x (cong pred p ; sym (suc-distrib-lefts n x))

  dyck→tree⊙-inj : (vs : Vec Tree (suc k)) → (xs ys : Dyck n) → dyck→tree⊙ vs xs ≡ dyck→tree⊙ vs ys → xs ≡ ys
  dyck→tree⊙-inj vs done done xs≡ys = refl
  dyck→tree⊙-inj vs (⟨ xs) (⟨ ys) xs≡ys = cong ⟨_ (dyck→tree⊙-inj vs xs ys (reduce-inj xs≡ys))
  dyck→tree⊙-inj vs (⟩ xs) (⟩ ys) xs≡ys = cong ⟩_ (dyck→tree⊙-inj vs xs ys (cong tail xs≡ys))
  dyck→tree⊙-inj vs done (⟨ ys) xs≡ys = ⊥-elim (lefts-monot (sizes vs) ys (cong sizes xs≡ys ; sizes-lefts vs (⟨ ys)))
  dyck→tree⊙-inj vs (⟨ xs) done xs≡ys = ⊥-elim (lefts-monot (sizes vs) xs (cong sizes (sym xs≡ys) ; sizes-lefts vs (⟨ xs)))
  dyck→tree⊙-inj vs (⟨ xs) (⟩ ys) xs≡ys = ⊥-elim (reduce≢shift xs≡ys)
  dyck→tree⊙-inj vs (⟩ xs) (⟨ ys) xs≡ys = ⊥-elim (reduce≢shift (sym xs≡ys))

  dyck→tree-inj : (xs ys : Dyck 0) → dyck→tree xs ≡ dyck→tree ys → xs ≡ ys
  dyck→tree-inj xs ys xs≡ys = dyck→tree⊙-inj (leaf ∷ []) xs ys (cong (_∷ []) xs≡ys)

  dyck⇔tree : Dyck 0 ⇔ Tree
  dyck⇔tree = surj×inj⇒iso dyck→tree (λ y → tree→dyck y , dyck→tree→dyck y) dyck→tree-inj

module Left where
  reduce : Vec Tree (2 + n) → Vec Tree (1 + n)
  reduce (t₁ ∷ t₂ ∷ ts) = t₂ * t₁ ∷ ts

  shift : Vec Tree n → Vec Tree (1 + n)
  shift = leaf ∷_

  dyck→tree⊙ : Vec Tree (1 + n) → Dyck n → Vec Tree 1
  dyck→tree⊙ = foldlDyck (Vec Tree ∘ suc) reduce shift

  dyck→tree : Dyck zero → Tree
  dyck→tree = head ∘ dyck→tree⊙ (leaf ∷ [])

  tree→dyck⊙ : Tree → Dyck n → Dyck n
  tree→dyck⊙ leaf      d = d
  tree→dyck⊙ (xs * ys) d = tree→dyck⊙ xs (⟨ tree→dyck⊙ ys (⟩ d))

  tree→dyck : Tree → Dyck zero
  tree→dyck tr = tree→dyck⊙ tr done
