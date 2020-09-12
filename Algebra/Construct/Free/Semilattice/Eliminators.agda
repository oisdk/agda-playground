{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Eliminators where

open import Algebra.Construct.Free.Semilattice.Definition
open import Prelude
open import Algebra

record _⇘_ {a p} (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
  no-eta-equality
  constructor elim
  field
    ⟦_⟧-set : ∀ {xs} → isSet (P xs)
    ⟦_⟧[] : P []
    ⟦_⟧_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ⟦_⟧[]; f = ⟦_⟧_∷_⟨_⟩
  field
    ⟦_⟧-com : ∀ x y xs pxs →
      f x (y ∷ xs) (f y xs pxs) ≡[ i ≔ P (com x y xs i) ]≡
      f y (x ∷ xs) (f x xs pxs)
    ⟦_⟧-dup : ∀ x xs pxs →
      f x (x ∷ xs) (f x xs pxs) ≡[ i ≔ P (dup x xs i) ]≡
      f x xs pxs
  ⟦_⟧⇓ : ∀ xs → P xs
  ⟦ [] ⟧⇓ = z
  ⟦ x ∷ xs ⟧⇓ = f x xs ⟦ xs ⟧⇓
  ⟦ com x y xs i ⟧⇓ = ⟦_⟧-com x y xs ⟦ xs ⟧⇓  i
  ⟦ dup x xs i ⟧⇓ = ⟦_⟧-dup x xs ⟦ xs ⟧⇓ i
  ⟦ trunc xs ys x y i j ⟧⇓ =
      isOfHLevel→isOfHLevelDep 2
        (λ xs → ⟦_⟧-set {xs})
        ⟦ xs ⟧⇓ ⟦ ys ⟧⇓
        (cong ⟦_⟧⇓ x) (cong ⟦_⟧⇓ y)
        (trunc xs ys x y)
        i j
  {-# INLINE ⟦_⟧⇓ #-}
open _⇘_ public

infixr 0 ⇘-syntax
⇘-syntax = _⇘_
syntax ⇘-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒ Pxs

record _⇲_ {a p} (A : Type a) (P : 𝒦 A  → Type p) : Type (a ℓ⊔ p) where
  no-eta-equality
  constructor elim-prop
  field
    ∥_∥-prop : ∀ {xs} → isProp (P xs)
    ∥_∥[] : P []
    ∥_∥_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ∥_∥[]; f = ∥_∥_∷_⟨_⟩
  ∥_∥⇑ = elim
          (λ {xs} → isProp→isSet (∥_∥-prop {xs}))
          z f
          (λ x y xs pxs → toPathP (∥_∥-prop (transp (λ i → P (com x y xs i)) i0 (f x (y ∷ xs) (f y xs pxs))) (f y (x ∷ xs) (f x xs pxs))))
          (λ x xs pxs → toPathP (∥_∥-prop (transp (λ i → P (dup x xs i)) i0 (f x (x ∷ xs) (f x xs pxs))) (f x xs pxs) ))
  ∥_∥⇓ = ⟦ ∥_∥⇑ ⟧⇓
  {-# INLINE ∥_∥⇑ #-}
  {-# INLINE ∥_∥⇓ #-}

open _⇲_ public
elim-prop-syntax : ∀ {a p} → (A : Type a) → (𝒦 A → Type p) → Type (a ℓ⊔ p)
elim-prop-syntax = _⇲_

syntax elim-prop-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒∥ Pxs ∥

record _↘∥_∥ {a p} (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
  no-eta-equality
  constructor elim-to-prop
  field
    ∣_∣[] : P []
    ∣_∣_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ∣_∣[]; f = ∣_∣_∷_⟨_⟩
  open import HITs.PropositionalTruncation.Sugar
  open import HITs.PropositionalTruncation

  ∣_∣⇑ : xs ∈𝒦 A ⇒∥ ∥ P xs ∥ ∥
  ∣_∣⇑ = elim-prop squash ∣ z ∣ λ x xs ∣Pxs∣ → f x xs ∥$∥ ∣Pxs∣
  ∣_∣⇓ = ∥ ∣_∣⇑ ∥⇓


open _↘∥_∥ public
elim-to-prop-syntax : ∀ {a p} → (A : Type a) → (𝒦 A → Type p) → Type (a ℓ⊔ p)
elim-to-prop-syntax = _↘∥_∥

syntax elim-to-prop-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒∣ Pxs ∣

infixr 0 _↘_
record _↘_ {a b} (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  no-eta-equality
  constructor rec
  field
    [_]-set  : isSet B
    [_]_∷_   : A → B → B
    [_][]    : B
  private f = [_]_∷_; z = [_][]
  field
    [_]-dup  : ∀ x xs → f x (f x xs) ≡ f x xs
    [_]-com : ∀ x y xs → f x (f y xs) ≡ f y (f x xs)
  [_]↑ = elim
            [_]-set
            z
            (λ x _ xs → f x xs)
            (λ x y xs → [_]-com x y)
            (λ x xs → [_]-dup x)
  [_]↓ = ⟦ [_]↑ ⟧⇓
  {-# INLINE [_]↑ #-}
  {-# INLINE [_]↓ #-}
open _↘_ public

module _ {a p} {A : Type a} {P : 𝒦 A → Type p} where
    𝒦-elim-prop : (∀ {xs} → isProp (P xs)) →
                  (∀ x xs → P xs → P (x ∷ xs)) →
                  (P []) →
                  ∀ xs → P xs
    𝒦-elim-prop isPropB f n = go
      where
      go : ∀ xs → P xs
      go [] = n
      go (x ∷ xs) = f x xs (go xs)
      go (com x y xs j) = toPathP {A = λ i → P (com x y xs i)} (isPropB (transp (λ i → P (com x y xs i)) i0 (f x (y ∷ xs) (f y xs (go xs)))) (f y (x ∷ xs) (f x xs (go xs)))) j
      go (dup x xs j) = toPathP {A = λ i → P (dup x xs i)} (isPropB (transp (λ i → P (dup x xs i)) i0 (f x (x ∷ xs) (f x xs (go xs)))) (f x xs (go xs)) ) j
      go (trunc xs ys x y i j) =
        isOfHLevel→isOfHLevelDep 2
          (λ xs → isProp→isSet (isPropB {xs}))
          (go xs) (go ys)
          (cong go x) (cong go y)
          (trunc xs ys x y)
          i j

module _ {a b} {A : Type a} {B : Type b} where
  𝒦-rec : isSet B →
          (f : A → B → B) →
          (n : B) →
          (fdup : ∀ x xs → f x (f x xs) ≡ f x xs) →
          (fcom : ∀ x y xs → f x (f y xs) ≡ f y (f x xs)) →
          𝒦 A →
          B
  𝒦-rec isSetB f n fdup fcom = go
    where
    go : 𝒦 A → B
    go [] = n
    go (x ∷ xs) = f x (go xs)
    go (com x y xs i) = fcom x y (go xs) i
    go (dup x xs i) = fdup x (go xs) i
    go (trunc xs ys x y i j) =
      isOfHLevel→isOfHLevelDep 2
        (λ xs → isSetB)
        (go xs) (go ys)
        (cong go x) (cong go y)
        (trunc xs ys x y)
        i j
