{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Union where

open import Prelude
open import Path.Reasoning
open import Algebra

open import Algebra.Construct.Free.Semilattice.Definition
open import Algebra.Construct.Free.Semilattice.Eliminators

infixr 5 _∪_
_∪_ : 𝒦 A → 𝒦 A → 𝒦 A
_∪_ = λ xs ys → [ union′ ys ]↓ xs
  where
  union′ : 𝒦 A → A ↘ 𝒦 A
  [ union′ ys ]-set = trunc
  [ union′ ys ] x ∷ xs = x ∷ xs
  [ union′ ys ][] = ys
  [ union′ ys ]-dup = dup
  [ union′ ys ]-com = com

∪-assoc : (xs ys zs : 𝒦 A) → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs)
∪-assoc = λ xs ys zs → ∥ ∪-assoc′ ys zs ∥⇓ xs
  where
  ∪-assoc′ : (ys zs : 𝒦 A) → xs ∈𝒦 A ⇒∥ (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs) ∥
  ∥ ∪-assoc′ ys zs ∥-prop = trunc _ _
  ∥ ∪-assoc′ ys zs ∥[] = refl
  ∥ ∪-assoc′ ys zs ∥ x ∷ xs ⟨ Pxs ⟩ = cong (x ∷_) Pxs

∪-identityʳ : (xs : 𝒦 A) → xs ∪ [] ≡ xs
∪-identityʳ = ∥ ∪-identityʳ′ ∥⇓
  where
  ∪-identityʳ′ : xs ∈𝒦 A ⇒∥ xs ∪ [] ≡ xs ∥
  ∥ ∪-identityʳ′ ∥-prop = trunc _ _
  ∥ ∪-identityʳ′ ∥[] = refl
  ∥ ∪-identityʳ′ ∥ x ∷ xs ⟨ Pxs ⟩ = cong (x ∷_) Pxs

cons-distrib-∪ : (x : A) (xs ys : 𝒦 A) → x ∷ xs ∪ ys ≡ xs ∪ (x ∷ ys)
cons-distrib-∪ = λ x xs ys → ∥ cons-distrib-∪′ x ys ∥⇓ xs
  where
  cons-distrib-∪′ : (x : A) (ys : 𝒦 A) → xs ∈𝒦 A ⇒∥ x ∷ xs ∪ ys ≡ xs ∪ (x ∷ ys) ∥
  ∥ cons-distrib-∪′ x ys ∥-prop = trunc _ _
  ∥ cons-distrib-∪′ x ys ∥[] = refl
  ∥ cons-distrib-∪′ x ys ∥ z ∷ xs ⟨ Pxs ⟩ =
    x ∷ ((z ∷ xs) ∪ ys) ≡⟨⟩
    x ∷ z ∷ (xs ∪ ys) ≡⟨ com x z (xs ∪ ys) ⟩
    z ∷ x ∷ (xs ∪ ys) ≡⟨ cong (z ∷_) Pxs ⟩
    ((z ∷ xs) ∪ (x ∷ ys)) ∎

∪-comm : (xs ys : 𝒦 A) → xs ∪ ys ≡ ys ∪ xs
∪-comm = λ xs ys → ∥ ∪-comm′ ys ∥⇓ xs
  where
  ∪-comm′ : (ys : 𝒦 A) → xs ∈𝒦 A ⇒∥ xs ∪ ys ≡ ys ∪ xs ∥
  ∥ ∪-comm′ ys ∥-prop = trunc _ _
  ∥ ∪-comm′ ys ∥[] = sym (∪-identityʳ ys)
  ∥ ∪-comm′ ys ∥ x ∷ xs ⟨ Pxs ⟩ =
    (x ∷ xs) ∪ ys ≡⟨⟩
    x ∷ (xs ∪ ys) ≡⟨ cong (x ∷_) Pxs ⟩
    x ∷ (ys ∪ xs) ≡⟨⟩
    (x ∷ ys) ∪ xs ≡⟨ cons-distrib-∪ x ys xs ⟩
    ys ∪ (x ∷ xs) ∎

∪-idem : (xs : 𝒦 A) → xs ∪ xs ≡ xs
∪-idem = ∥ ∪-idem′ ∥⇓
  where
  ∪-idem′ : xs ∈𝒦 A ⇒∥ xs ∪ xs ≡ xs ∥
  ∥ ∪-idem′ ∥-prop = trunc _ _
  ∥ ∪-idem′ ∥[] = refl
  ∥ ∪-idem′ ∥ x ∷ xs ⟨ Pxs ⟩ =
    ((x ∷ xs) ∪ (x ∷ xs)) ≡˘⟨ cons-distrib-∪ x (x ∷ xs) xs ⟩
    x ∷ x ∷ (xs ∪ xs) ≡⟨ dup x (xs ∪ xs) ⟩
    x ∷ (xs ∪ xs) ≡⟨ cong (x ∷_) Pxs ⟩
    x ∷ xs ∎

module _ {a} {A : Type a} where
  open Semilattice
  open CommutativeMonoid
  open Monoid
  𝒦-semilattice : Semilattice a
  𝒦-semilattice .commutativeMonoid .monoid .𝑆 = 𝒦 A
  𝒦-semilattice .commutativeMonoid .monoid ._∙_ = _∪_
  𝒦-semilattice .commutativeMonoid .monoid .ε = []
  𝒦-semilattice .commutativeMonoid .monoid .assoc = ∪-assoc
  𝒦-semilattice .commutativeMonoid .monoid .ε∙ _ = refl
  𝒦-semilattice .commutativeMonoid .monoid .∙ε = ∪-identityʳ
  𝒦-semilattice .commutativeMonoid .comm = ∪-comm
  𝒦-semilattice .idem = ∪-idem
