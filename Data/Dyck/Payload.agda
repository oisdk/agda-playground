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
-- Conversion between binary trees and Progs. (rightwards)
--------------------------------------------------------------------------------

module Right where
  data Prog {a} (A : Type a) : ℕ → Type a where
    halt : Prog A zero
    push : Prog A (suc n) → Prog A n
    pull : A → Prog A n → Prog A (suc n)

  foldrProg : (P : ℕ → Type b) → (∀ {n} → P (suc n) → P n) → (∀ {n} → A → P n → P (suc n)) → P zero → Prog A n → P n
  foldrProg P l r h halt        = h
  foldrProg P l r h (push   ds) = l (foldrProg P l r h ds)
  foldrProg P l r h (pull x ds) = r x (foldrProg P l r h ds)

  tree→prog⊙ : Tree A → Prog A n → A × Prog A n
  tree→prog⊙ [ x ]     = x ,_
  tree→prog⊙ (xs * ys) = map₂ push ∘ tree→prog⊙ xs ∘ uncurry pull ∘ tree→prog⊙ ys

  -- Tree to Prog
  tree→prog : Tree A → A × Prog A zero
  tree→prog t = tree→prog⊙ t halt

  reduce : Vec (Tree A) (2 + n) → Vec (Tree A) (suc n)
  reduce (x ∷ y ∷ xs) = (x * y) ∷ xs

  shift : A → Vec (Tree A) n → Vec (Tree A) (suc n)
  shift x = [ x ] ∷_

  prog→tree⊙ : Vec (Tree A) (suc k) → Prog A n → Vec (Tree A) (suc n + k)
  prog→tree⊙ = foldrProg (λ n → Vec (Tree _) (suc n + _)) reduce shift

  -- Prog to tree
  prog→tree : A × Prog A zero → Tree A
  prog→tree (x , xs) = head (prog→tree⊙ ([ x ] ∷ []) xs)

--   prog→tree→prog-pop : ∀ (xs : Vec Tree (suc k)) (d : Prog n) t → prog→tree⊙ xs (tree→prog⊙ t (⟩ d)) ≡ t ∷ prog→tree⊙ xs d
--   prog→tree→prog-pop xs d leaf = refl
--   prog→tree→prog-pop xs d (ls * rs) =
--     prog→tree⊙ xs (⟨ tree→prog⊙ ls (⟩ tree→prog⊙ rs (⟩ d)))        ≡⟨⟩
--     reduce (prog→tree⊙ xs (tree→prog⊙ ls (⟩ tree→prog⊙ rs (⟩ d)))) ≡⟨ cong reduce (prog→tree→prog-pop xs (tree→prog⊙ rs (⟩ d)) ls) ⟩
--     reduce (ls ∷ prog→tree⊙ xs (tree→prog⊙ rs (⟩ d)))              ≡⟨ cong reduce (cong (ls ∷_) (prog→tree→prog-pop xs d rs)) ⟩
--     reduce (ls ∷ rs ∷ prog→tree⊙ xs d)                             ≡⟨⟩
--     (ls * rs) ∷ prog→tree⊙ xs d ∎

--   prog→tree→prog-push : ∀ t (xs : Vec Tree n) → prog→tree⊙ (leaf ∷ xs) (tree→prog t) ≡ t ∷ xs
--   prog→tree→prog-push leaf      xs = refl
--   prog→tree→prog-push (ls * rs) xs =
--     prog→tree⊙ (leaf ∷ xs) (tree→prog (ls * rs))                     ≡⟨⟩
--     reduce (prog→tree⊙ (leaf ∷ xs) (tree→prog⊙ ls (⟩ tree→prog rs))) ≡⟨ cong reduce (prog→tree→prog-pop (leaf ∷ xs) (tree→prog rs) ls ) ⟩
--     reduce (ls ∷ prog→tree⊙ (leaf ∷ xs) (tree→prog rs))              ≡⟨ cong reduce (cong (ls ∷_) (prog→tree→prog-push rs xs)) ⟩
--     (ls * rs) ∷ xs ∎

--   prog→tree→prog : ∀ t → prog→tree (tree→prog t) ≡ t
--   prog→tree→prog t = cong head (prog→tree→prog-push t [])

--   unreduce : Vec Tree (suc n) → Vec Tree (2 + n)
--   unreduce (leaf ∷ xs) = leaf ∷ leaf ∷ xs
--   unreduce ((x₁ * x₂) ∷ xs) = x₁ ∷ x₂ ∷ xs

--   reduce-inj : {xs ys : Vec Tree (2 + n)} → reduce xs ≡ reduce ys → xs ≡ ys
--   reduce-inj xs≡ys = cong unreduce xs≡ys

--   sizes⊙ : Vec Tree n → ℕ → ℕ
--   sizes⊙ xs n = foldr′ size⊙ n xs

--   lefts⊙ : Prog n → ℕ → ℕ
--   lefts⊙ halt n = n
--   lefts⊙ (⟨ d) n = suc (lefts⊙ d n)
--   lefts⊙ (⟩ d) n = lefts⊙ d n

--   sizes : Vec Tree n → ℕ
--   sizes xs = sizes⊙ xs 0

--   reduce≢shift : {xs : Vec Tree (2 + n)} → {ys : Vec Tree n} → reduce xs ≢ shift ys
--   reduce≢shift = snotz ∘ cong (size ∘ head)

--   sizes-lefts : (vs : Vec Tree (suc k)) → (xs : Prog n) → sizes⊙ (prog→tree⊙ vs xs) m ≡ lefts⊙ xs (sizes⊙ vs m)
--   sizes-lefts vs halt   = refl
--   sizes-lefts vs (⟨ xs) = cong suc (sizes-lefts vs xs)
--   sizes-lefts vs (⟩ xs) = sizes-lefts vs xs

--   suc-distrib-lefts : ∀ n (x : Prog m) → suc (lefts⊙ x n) ≡ lefts⊙ x (suc n)
--   suc-distrib-lefts n halt = refl
--   suc-distrib-lefts n (⟨ x) = cong suc (suc-distrib-lefts n x)
--   suc-distrib-lefts n (⟩ x) = suc-distrib-lefts n x

--   lefts-monot : ∀ n (x : Prog m) → n ≢ suc (lefts⊙ x n)
--   lefts-monot zero x p = znots p
--   lefts-monot (suc n) x p = lefts-monot n x (cong pred p ; sym (suc-distrib-lefts n x))

--   prog→tree⊙-inj : (vs : Vec Tree (suc k)) → (xs ys : Prog n) → prog→tree⊙ vs xs ≡ prog→tree⊙ vs ys → xs ≡ ys
--   prog→tree⊙-inj vs halt halt xs≡ys = refl
--   prog→tree⊙-inj vs (⟨ xs) (⟨ ys) xs≡ys = cong ⟨_ (prog→tree⊙-inj vs xs ys (reduce-inj xs≡ys))
--   prog→tree⊙-inj vs (⟩ xs) (⟩ ys) xs≡ys = cong pull (prog→tree⊙-inj vs xs ys (cong tail xs≡ys))
--   prog→tree⊙-inj vs halt (⟨ ys) xs≡ys = ⊥-elim (lefts-monot (sizes vs) ys (cong sizes xs≡ys ; sizes-lefts vs (⟨ ys)))
--   prog→tree⊙-inj vs (⟨ xs) halt xs≡ys = ⊥-elim (lefts-monot (sizes vs) xs (cong sizes (sym xs≡ys) ; sizes-lefts vs (⟨ xs)))
--   prog→tree⊙-inj vs (⟨ xs) (⟩ ys) xs≡ys = ⊥-elim (reduce≢shift xs≡ys)
--   prog→tree⊙-inj vs (⟩ xs) (⟨ ys) xs≡ys = ⊥-elim (reduce≢shift (sym xs≡ys))

--   prog→tree-inj : (xs ys : Prog 0) → prog→tree xs ≡ prog→tree ys → xs ≡ ys
--   prog→tree-inj xs ys xs≡ys = prog→tree⊙-inj (leaf ∷ []) xs ys (cong (_∷ []) xs≡ys)

--   prog⇔tree : Prog 0 ⇔ Tree
--   prog⇔tree = surj×inj⇒iso prog→tree (λ y → tree→prog y , prog→tree→prog y) prog→tree-inj

module Left where

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
