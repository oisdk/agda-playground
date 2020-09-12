{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Extensionality where

open import Prelude

open import Algebra.Construct.Free.Semilattice.Definition
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Relation.Unary
open import Algebra.Construct.Free.Semilattice.Union

open import HITs.PropositionalTruncation.Sugar
import HITs.PropositionalTruncation as PropTrunc
open import HITs.PropositionalTruncation.Properties

open import Path.Reasoning

infix 4 _↭_
_↭_ : 𝒦 A → 𝒦 A → Type _
xs ↭ ys = ∀ x → x ∈ xs ↔ x ∈ ys

in-cons : (x : A) (xs : 𝒦 A) → x ∈ xs → xs ≡ x ∷ xs
in-cons = λ x → ∥ in-cons′ x ∥⇓
  where
  in-cons′ : ∀ x → xs ∈𝒦 A ⇒∥ (x ∈ xs → xs ≡ x ∷ xs) ∥
  ∥ in-cons′ y ∥-prop {xs} p q i y∈xs = trunc xs (y ∷ xs) (p y∈xs) (q y∈xs) i
  ∥ in-cons′ y ∥[] ()
  ∥ in-cons′ y ∥ x ∷ xs ⟨ Pxs ⟩ = PropTrunc.rec (trunc _ _)
    λ { (inl x≡y) → sym (dup x xs) ; cong (_∷ x ∷ xs) x≡y
      ; (inr y∈xs) → cong (x ∷_) (Pxs y∈xs) ; com x y xs
      }

subset-ext : ∀ xs ys → (∀ (x : A) → x ∈ xs → x ∈ ys) → xs ∪ ys ≡ ys
subset-ext = ∥ subset-ext′ ∥⇓
  where
  subset-ext′ : xs ∈𝒦 A ⇒∥ (∀ ys → (∀ x → x ∈ xs → x ∈ ys) → xs ∪ ys ≡ ys) ∥
  ∥ subset-ext′ ∥-prop {xs} p q i ys perm = trunc (xs ∪ ys) ys (p ys perm) (q ys perm) i
  ∥ subset-ext′ ∥[] _ _ = refl
  ∥ subset-ext′ ∥ x ∷ xs ⟨ Pxs ⟩ ys perm =
    (x ∷ xs) ∪ ys ≡⟨ cons-distrib-∪ x xs ys ⟩
    xs ∪ (x ∷ ys) ≡⟨ Pxs (x ∷ ys) (λ y y∈xs → ∣ inr (perm y ∣ inr y∈xs ∣) ∣) ⟩
    x ∷ ys ≡˘⟨ in-cons x ys (perm x ∣ inl refl ∣) ⟩
    ys ∎

extensional : (xs ys : 𝒦 A) → (xs ↭ ys) → xs ≡ ys
extensional xs ys xs↭ys =
  xs ≡˘⟨ subset-ext ys xs (inv ∘ xs↭ys) ⟩
  ys ∪ xs ≡⟨ ∪-comm ys xs ⟩
  xs ∪ ys ≡⟨ subset-ext xs ys (fun ∘ xs↭ys) ⟩
  ys ∎
