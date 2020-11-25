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
shift xs = leaf ∷ xs

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

-- tree→dyck-inj : Injective tree→dyck
-- tree→dyck-inj leaf leaf xs≡ys = refl
-- tree→dyck-inj leaf (ys * ys₁) xs≡ys = {!!}
-- tree→dyck-inj (xs * xs₁) leaf xs≡ys = {!!}
-- tree→dyck-inj (xs * xs₁) (ys * ys₁) xs≡ys = {!!}

-- -- tree↣dyck : Tree ↣ Dyck zero
-- -- tree↣dyck .fst = tree→dyck
-- -- tree↣dyck .snd x y x₁ = {!!}

-- -- dyck-conc : Dyck n → Dyck m → Dyck (n + m)
-- -- dyck-conc done ys = ys
-- -- dyck-conc (⟨ xs) ys = ⟨ dyck-conc xs ys
-- -- dyck-conc (⟩ xs) ys = ⟩ dyck-conc xs ys


-- -- dyck→tree→dyck⊙ : (d d′ : Dyck n) → tree→dyck⊙ (dyck→tree d) d′ ≡ dyck-conc d  d′
-- -- dyck→tree→dyck⊙ xs done  d′ = {!!}
-- -- dyck→tree→dyck⊙ xs (⟨ d) d′ = {!!}
-- -- dyck→tree→dyck⊙ xs (⟩ d) d′ = {!!}

-- -- dyck→tree→dyck′ : (d : Dyck zero) → tree→dyck (dyck→tree d) ≡ d
-- -- dyck→tree→dyck′ d = dyck→tree→dyck⊙ (leaf ∷ []) d done
