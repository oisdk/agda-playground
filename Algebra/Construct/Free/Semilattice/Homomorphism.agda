{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Homomorphism where

open import Prelude
open import Algebra
open import Path.Reasoning

open import Algebra.Construct.Free.Semilattice.Definition
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Union

module _ {b} (semilattice : Semilattice b) where
  open Semilattice semilattice
  module _ (sIsSet : isSet 𝑆) (h : A → 𝑆) where
    μ′ : A ↘ 𝑆
    [ μ′ ]-set = sIsSet
    [ μ′ ] x ∷ xs = h x ∙ xs
    [ μ′ ][] = ε
    [ μ′ ]-dup x xs =
      h x ∙ (h x ∙ xs) ≡˘⟨ assoc (h x) (h x) xs ⟩
      (h x ∙ h x) ∙ xs ≡⟨ cong (_∙ xs) (idem (h x)) ⟩
      h x ∙ xs ∎
    [ μ′ ]-com x y xs =
      h x ∙ (h y ∙ xs) ≡˘⟨ assoc (h x) (h y) xs ⟩
      (h x ∙ h y) ∙ xs ≡⟨ cong (_∙ xs) (comm (h x) (h y)) ⟩
      (h y ∙ h x) ∙ xs ≡⟨ assoc (h y) (h x) xs ⟩
      h y ∙ (h x ∙ xs) ∎

    μ : 𝒦 A → 𝑆
    μ = [ μ′ ]↓

    ∙-hom′ : ∀ ys → xs ∈𝒦 A ⇒∥ μ xs ∙ μ ys ≡ μ (xs ∪ ys) ∥
    ∥ ∙-hom′ ys ∥-prop = sIsSet _ _
    ∥ ∙-hom′ ys ∥[] = ε∙ _
    ∥ ∙-hom′ ys ∥ x ∷ xs ⟨ Pxs ⟩ =
      μ (x ∷ xs) ∙ μ ys ≡⟨⟩
      (h x ∙ μ xs) ∙ μ ys ≡⟨ assoc (h x) (μ xs) (μ ys) ⟩
      h x ∙ (μ xs ∙ μ ys) ≡⟨ cong (h x ∙_) Pxs ⟩
      h x ∙ μ (xs ∪ ys) ≡⟨⟩
      μ ((x ∷ xs) ∪ ys) ∎

    ∙-hom : ∀ xs ys → μ xs ∙ μ ys ≡ μ (xs ∪ ys)
    ∙-hom xs ys = ∥ ∙-hom′ ys ∥⇓ xs
