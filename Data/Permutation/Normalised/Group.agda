{-# OPTIONS --safe #-}

module Data.Permutation.Normalised.Group where

open import Prelude hiding (_↔_)
open import Data.List hiding ([]; _∷_)
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Permutation.Swap _≟_
open import Data.Permutation.NonNorm _≟_
open import Data.Nat using (_+_)
open import Data.Permutation.Normalised.Definition
open import Data.List.Properties
open import Data.Permutation.Normalised.Unnorm
open import Data.Permutation.Normalised.Norm
open import Data.Permutation.Normalised.RoundTrip
open import Data.Permutation.Normalised.Injective
open import Path.Reasoning


⊕-from : Diffs → Diffs → ℕ → Diffs
⊕-from xs ys n = foldr (flip _⊙⟨_⟩) xs (un-diff ys n)

infixl 6 _⊕_
_⊕_ : Diffs → Diffs → Diffs
xs ⊕ ys = ⊕-from xs ys 0

diffs-comp-lemma : ∀ xs ys m n → foldr (flip _⊙⟨_⟩) xs (un-diff ys m) ⊙ n ≡ xs ⊙ (ys ⊙+ m ⊙ n)
diffs-comp-lemma xs ⟨⟩ m n = refl
diffs-comp-lemma xs (ys ∘⟨ x , y ⟩) m n =
  ⊕-from xs (ys ∘⟨ x , y ⟩) m ⊙ n ≡⟨⟩
  ⊕-from xs ys (suc m + x) ⊙⟨ m + x , y ⟩ ⊙ n ≡⟨ cons-swap (m + x) y (⊕-from xs ys (suc m + x)) n ⟩
  ⊕-from xs ys (suc m + x) ⊙ m + x ↔ y ⊙ n ≡⟨ diffs-comp-lemma xs ys (suc m + x) _ ⟩
  (xs ⊙ ys ⊙+ suc m + x ⊙ m + x ↔ y ⊙ n) ≡˘⟨ cong (xs ⊙_) (⊙-alg-com (m + x) y ys n ) ⟩
  (xs ⊙ ys ∘⟨ m + x , y ⟩ ⊙ n) ≡⟨⟩
  (xs ⊙ ys ∘⟨ x , y ⟩ ⊙+ m ⊙ n) ∎

diffs-comp : ∀ xs ys n → (xs ⊕ ys) ⊙ n ≡ xs ⊙ (ys ⊙ n)
diffs-comp xs ys n =
  xs ⊕ ys ⊙ n ≡⟨ diffs-comp-lemma xs ys 0 n  ⟩
  xs ⊙ (ys ⊙+ 0 ⊙ n) ≡⟨ cong (λ e → xs ⊙ e ⊙ n) (shift-0 ys) ⟩
  xs ⊙ ys ⊙ n ∎

⊕-hom : ∀ xs ys → [ xs ∙ ys ]↓ ≡ [ xs ]↓ ⊕ [ ys ]↓
⊕-hom xs ys =
  inj-⊙ [ xs ∙ ys ]↓ ([ xs ]↓ ⊕ [ ys ]↓) λ n →
  [ xs ∙ ys ]↓ ⊙ n ≡⟨ ⊙↓-hom (xs ∙ ys) n ⟩
  xs ∙ ys · n ≡⟨ ∙-· xs ys n ⟩
  xs · ys · n ≡˘⟨ ⊙↓-hom xs (ys · n) ⟩
  [ xs ]↓ ⊙ ys · n ≡˘⟨ cong ([ xs ]↓ ⊙_) (⊙↓-hom ys n) ⟩
  [ xs ]↓ ⊙ [ ys ]↓ ⊙ n ≡˘⟨ diffs-comp [ xs ]↓ [ ys ]↓ n ⟩
  [ xs ]↓ ⊕ [ ys ]↓ ⊙ n ∎


⊕-assoc : ∀ xs ys zs → (xs ⊕ ys) ⊕ zs ≡ xs ⊕ (ys ⊕ zs)
⊕-assoc xs ys zs =
  (xs ⊕ ys) ⊕ zs ≡˘⟨ cong₃ (λ x y z → (x ⊕ y) ⊕ z) (norm-inv xs) (norm-inv ys) (norm-inv zs) ⟩
  ([ [ xs ]↑ ]↓ ⊕ [ [ ys ]↑ ]↓) ⊕ [ [ zs ]↑ ]↓ ≡˘⟨ cong (_⊕ [ [ zs ]↑ ]↓) (⊕-hom [ xs ]↑ [ ys ]↑) ⟩
  [ [ xs ]↑ ∙ [ ys ]↑ ]↓ ⊕ [ [ zs ]↑ ]↓ ≡˘⟨ ⊕-hom ([ xs ]↑ ∙ [ ys ]↑) [ zs ]↑ ⟩
  [ ([ xs ]↑ ∙ [ ys ]↑) ∙ [ zs ]↑ ]↓ ≡⟨ cong [_]↓ (∙-assoc [ xs ]↑ [ ys ]↑ [ zs ]↑) ⟩ 
  [ [ xs ]↑ ∙ ([ ys ]↑ ∙ [ zs ]↑) ]↓ ≡⟨ ⊕-hom [ xs ]↑ ([ ys ]↑ ∙ [ zs ]↑) ⟩
  [ [ xs ]↑ ]↓ ⊕ ([ [ ys ]↑ ∙ [ zs ]↑ ]↓) ≡⟨ cong ([ [ xs ]↑ ]↓ ⊕_) (⊕-hom [ ys ]↑ [ zs ]↑) ⟩
  [ [ xs ]↑ ]↓ ⊕ ([ [ ys ]↑ ]↓ ⊕ [ [ zs ]↑ ]↓) ≡⟨ cong₃ (λ x y z → x ⊕ (y ⊕ z)) (norm-inv xs) (norm-inv ys) (norm-inv zs) ⟩
  xs ⊕ (ys ⊕ zs) ∎

negate : Diffs → Diffs
negate xs = [ neg [ xs ]↑ ]↓

neg-inv-d : ∀ xs → xs ⊕ negate xs ≡ ⟨⟩
neg-inv-d xs = inj-⊙ _ _ λ n →
  xs ⊕ negate xs ⊙ n ≡⟨⟩
  xs ⊕ [ neg [ xs ]↑ ]↓ ⊙ n ≡˘⟨ cong (λ e → e ⊕ [ neg [ xs ]↑ ]↓ ⊙ n) (norm-inv xs) ⟩
  [ [ xs ]↑ ]↓ ⊕ [ neg [ xs ]↑ ]↓ ⊙ n ≡˘⟨ cong (_⊙ n) (⊕-hom [ xs ]↑ (neg [ xs ]↑)) ⟩
  [ [ xs ]↑ ∙ neg [ xs ]↑ ]↓ ⊙ n ≡⟨ ⊙↓-hom ([ xs ]↑ ∙ neg [ xs ]↑) n ⟩
  [ xs ]↑ ∙ neg [ xs ]↑ · n ≡⟨ neg-id [ xs ]↑ n ⟩
  ⟨⟩ ⊙ n ∎
