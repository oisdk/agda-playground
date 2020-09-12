{-# OPTIONS --cubical --safe --postfix-projections #-}

module Algebra.Construct.Free.Semilattice.Direct where

open import Algebra
open import Prelude
open import Path.Reasoning
infixl 6 _∪_

data 𝒦 (A : Type a) : Type a where
  η : A → 𝒦 A
  _∪_ : 𝒦 A → 𝒦 A → 𝒦 A
  ∅ : 𝒦 A
  ∪-assoc : ∀ xs ys zs → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs)
  ∪-commutative : ∀ xs ys → xs ∪ ys ≡ ys ∪ xs
  ∪-idempotent : ∀ xs → xs ∪ xs ≡ xs
  ∪-identity : ∀ xs → xs ∪ ∅ ≡ xs
  trunc : isSet (𝒦 A)

module _ (semiLattice : Semilattice b) where
  open Semilattice semiLattice
  module _ (sIsSet : isSet 𝑆) (h : A → 𝑆) where
    μ : 𝒦 A → 𝑆
    μ (η x) = h x
    μ (xs ∪ ys) = μ xs ∙ μ ys
    μ ∅ = ε
    μ (∪-assoc xs ys zs i) = assoc (μ xs) (μ ys) (μ zs) i
    μ (∪-commutative xs ys i) = comm (μ xs) (μ ys) i
    μ (∪-idempotent xs i) = idem (μ xs) i
    μ (∪-identity xs i) = ∙ε (μ xs) i
    μ (trunc xs ys x y i j) = sIsSet (μ xs) (μ ys) (cong μ x) (cong μ y) i j

module Eliminators where
  record _⇘_ {a p} (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
    constructor elim
    field
      ⟦_⟧-set : ∀ {xs} → isSet (P xs)
      ⟦_⟧∅ : P ∅
      ⟦_⟧_∪_⟨_∪_⟩ : ∀ xs ys → P xs → P ys → P (xs ∪ ys)
      ⟦_⟧η : ∀ x → P (η x)
    private z = ⟦_⟧∅; f = ⟦_⟧_∪_⟨_∪_⟩
    field
      ⟦_⟧-assoc : ∀ xs ys zs pxs pys pzs →
        f (xs ∪ ys) zs (f xs ys pxs pys) pzs ≡[ i ≔ P (∪-assoc xs ys zs i ) ]≡
        f xs (ys ∪ zs) pxs (f ys zs pys pzs)
      ⟦_⟧-commutative : ∀ xs ys pxs pys →
        f xs ys pxs pys ≡[ i ≔ P (∪-commutative xs ys i) ]≡ f ys xs pys pxs
      ⟦_⟧-idempotent : ∀ xs pxs →
        f xs xs pxs pxs ≡[ i ≔ P (∪-idempotent xs i) ]≡ pxs
      ⟦_⟧-identity : ∀ xs pxs → f xs ∅ pxs z ≡[ i ≔ P (∪-identity xs i) ]≡ pxs
    ⟦_⟧⇓ : ∀ xs → P xs
    ⟦ η x ⟧⇓ = ⟦_⟧η x
    ⟦ xs ∪ ys ⟧⇓ = f xs ys ⟦ xs ⟧⇓ ⟦ ys ⟧⇓
    ⟦ ∅ ⟧⇓ = z
    ⟦ ∪-assoc xs ys zs i ⟧⇓ = ⟦_⟧-assoc xs ys zs ⟦ xs ⟧⇓ ⟦ ys ⟧⇓ ⟦ zs ⟧⇓ i
    ⟦ ∪-commutative xs ys i ⟧⇓ = ⟦_⟧-commutative xs ys ⟦ xs ⟧⇓ ⟦ ys ⟧⇓ i
    ⟦ ∪-idempotent xs i ⟧⇓ = ⟦_⟧-idempotent xs ⟦ xs ⟧⇓ i
    ⟦ ∪-identity xs i ⟧⇓ = ⟦_⟧-identity xs ⟦ xs ⟧⇓ i
    ⟦ trunc xs ys x y i j ⟧⇓ =
        isOfHLevel→isOfHLevelDep 2
          (λ xs → ⟦_⟧-set {xs})
          ⟦ xs ⟧⇓ ⟦ ys ⟧⇓
          (cong ⟦_⟧⇓ x) (cong ⟦_⟧⇓ y)
          (trunc xs ys x y)
          i j
  open _⇘_ public

  infixr 0 ⇘-syntax
  ⇘-syntax = _⇘_
  syntax ⇘-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒ Pxs

  record _⇲_ {a p} (A : Type a) (P : 𝒦 A  → Type p) : Type (a ℓ⊔ p) where
    constructor elim-prop
    field
      ∥_∥-prop : ∀ {xs} → isProp (P xs)
      ∥_∥∅ : P ∅
      ∥_∥_∪_⟨_∪_⟩ : ∀ xs ys → P xs → P ys → P (xs ∪ ys)
      ∥_∥η : ∀ x → P (η x)
    private z = ∥_∥∅; f = ∥_∥_∪_⟨_∪_⟩
    ∥_∥⇑ = elim
            (λ {xs} → isProp→isSet (∥_∥-prop {xs}))
            z f ∥_∥η
            (λ xs ys zs pxs pys pzs → toPathP (∥_∥-prop (transp (λ i → P (∪-assoc xs ys zs i)) i0 (f (xs ∪ ys) zs (f xs ys pxs pys) pzs)) (f xs (ys ∪ zs) pxs (f ys zs pys pzs) )))
            (λ xs ys pxs pys → toPathP (∥_∥-prop (transp (λ i → P (∪-commutative xs ys i)) i0 (f xs ys pxs pys)) (f ys xs pys pxs) ))
            (λ xs pxs → toPathP (∥_∥-prop (transp (λ i → P (∪-idempotent xs i)) i0 (f xs xs pxs pxs)) pxs))
            (λ xs pxs → toPathP (∥_∥-prop (transp (λ i → P (∪-identity xs i)) i0 (f xs ∅ pxs z)) pxs))
    ∥_∥⇓ = ⟦ ∥_∥⇑ ⟧⇓

  open _⇲_ public
  elim-prop-syntax : ∀ {a p} → (A : Type a) → (𝒦 A → Type p) → Type (a ℓ⊔ p)
  elim-prop-syntax = _⇲_

  syntax elim-prop-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒∥ Pxs ∥

module _ {a} {A : Type a} where
  open Semilattice
  open CommutativeMonoid
  open Monoid
  𝒦-semilattice : Semilattice a
  𝒦-semilattice .commutativeMonoid .monoid .𝑆 = 𝒦 A
  𝒦-semilattice .commutativeMonoid .monoid ._∙_ = _∪_
  𝒦-semilattice .commutativeMonoid .monoid .ε = ∅
  𝒦-semilattice .commutativeMonoid .monoid .assoc = ∪-assoc
  𝒦-semilattice .commutativeMonoid .monoid .ε∙ x = ∪-commutative ∅ x ; ∪-identity x
  𝒦-semilattice .commutativeMonoid .monoid .∙ε = ∪-identity
  𝒦-semilattice .commutativeMonoid .comm = ∪-commutative
  𝒦-semilattice .idem = ∪-idempotent

import Algebra.Construct.Free.Semilattice as Listed

Listed→Direct : Listed.𝒦 A → 𝒦 A
Listed→Direct = Listed.μ 𝒦-semilattice trunc η

Direct→Listed : 𝒦 A → Listed.𝒦 A
Direct→Listed = μ Listed.𝒦-semilattice Listed.trunc (Listed._∷ Listed.[])

Listed→Direct→Listed : (xs : Listed.𝒦 A) → Direct→Listed (Listed→Direct xs) ≡ xs
Listed→Direct→Listed = ∥ ldl ∥⇓
  where
  open Listed using (_⇲_; elim-prop-syntax)
  open _⇲_

  ldl : xs ∈𝒦 A ⇒∥ Direct→Listed (Listed→Direct xs) ≡ xs ∥
  ∥ ldl ∥-prop = Listed.trunc _ _
  ∥ ldl ∥[] = refl
  ∥ ldl ∥ x ∷ xs ⟨ Pxs ⟩ = cong (x Listed.∷_) Pxs

open Eliminators

Direct→Listed→Direct : (xs : 𝒦 A) → Listed→Direct (Direct→Listed xs) ≡ xs
Direct→Listed→Direct = ∥ dld ∥⇓
  where
  dld : xs ∈𝒦 A ⇒∥ Listed→Direct (Direct→Listed xs) ≡ xs ∥
  ∥ dld ∥-prop = trunc _ _
  ∥ dld ∥∅ = refl
  ∥ dld ∥η x = ∪-identity (η x)
  ∥ dld ∥ xs ∪ ys ⟨ Pxs ∪ Pys ⟩ =
    sym (Listed.∙-hom 𝒦-semilattice trunc η (Direct→Listed xs) (Direct→Listed ys)) ;
    cong₂ _∪_ Pxs Pys

Direct⇔Listed : 𝒦 A ⇔ Listed.𝒦 A
Direct⇔Listed .fun = Direct→Listed
Direct⇔Listed .inv = Listed→Direct
Direct⇔Listed .rightInv = Listed→Direct→Listed
Direct⇔Listed .leftInv = Direct→Listed→Direct
