{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Dist.Eliminators {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels
open import Control.Monad.Dist.Definition rng

private variable p : Level

record Eliminator (A : Type a) (P : W A → Type p) : Type (p ℓ⊔ a ℓ⊔ ℓ) where
  constructor elim
  field
    ⟦_⟧-set : ∀ {xs} → isSet (P xs)
    ⟦_⟧_&_∷_⟨_⟩ : ∀ w x xs → P xs → P (w & x ∷ xs)
    ⟦_⟧[] : P []
  private f = ⟦_⟧_&_∷_⟨_⟩; z = ⟦_⟧[]
  field
    ⟦_⟧-dup : ∀ p q x xs   pxs → f p x (q & x ∷ xs) (f q x xs pxs) ≡[ i ≔ P (dup p q x xs i) ]≡ f (p + q) x xs pxs
    ⟦_⟧-com : ∀ p x q y xs pxs → f p x (q & y ∷ xs) (f q y xs pxs) ≡[ i ≔ P (com p x q y xs i) ]≡ f q y (p & x ∷ xs) (f p x xs pxs)
    ⟦_⟧-del : ∀ x xs       pxs → f 0# x xs pxs                     ≡[ i ≔ P (del x xs i) ]≡ pxs

  run : (xs : W A) → P xs
  run [] = z
  run (p & x ∷ xs) = f p x xs (run xs)
  run (dup p q x xs i) = ⟦_⟧-dup p q x xs (run xs) i
  run (com p x q y xs i) = ⟦_⟧-com p x q y xs (run xs) i
  run (del x xs i) = ⟦_⟧-del x xs (run xs) i
  run (trunc xs ys p q i j) =
      isOfHLevel→isOfHLevelDep 2
        (λ xs → ⟦_⟧-set {xs})
        (run xs) (run ys)
        (cong run p) (cong run q)
        (trunc xs ys p q)
        i j

  _⇓_ : (xs : W A) → P xs
  _⇓_ = run
  {-# INLINE _⇓_ #-}

open Eliminator public
infixr 1 Eliminator

syntax Eliminator A (λ v → e) = W-Π[ v ⦂ e ] A

record Recursor (A : Type a) (B : Type b) : Type (a ℓ⊔ b ℓ⊔ ℓ) where
  constructor rec
  field
    [_]-set : isSet B
    [_]_&_∷_⟨_⟩ : (p : 𝑅) → (x : A) → (xs : W A) → B → B
    [_][] : B
  private f = [_]_&_∷_⟨_⟩; z = [_][]
  field
    [_]-dup : ∀ p q x xs   pxs → f p x (q & x ∷ xs) (f q x xs pxs) ≡ f (p + q) x xs pxs
    [_]-com : ∀ p x q y xs pxs → f p x (q & y ∷ xs) (f q y xs pxs) ≡ f q y (p & x ∷ xs) (f p x xs pxs)
    [_]-del : ∀ x xs       pxs → f 0# x xs pxs                     ≡ pxs

  _↑ : Eliminator A (λ _ → B)
  _↑ = elim [_]-set f z [_]-dup [_]-com [_]-del

  _↓_ : W A → B
  _↓_ = run _↑
  {-# INLINE _↑ #-}
  {-# INLINE _↓_ #-}
open Recursor public

infixr 1 Recursor

syntax Recursor A B = W-ϕ[ A ] B

infix 4 _⊜_
record AnEquality (A : Type a) : Type (a ℓ⊔ ℓ) where
  constructor _⊜_
  field lhs rhs : W A
open AnEquality public

record Property {r} (A : Type a) (P : W A → Type r) : Type (a ℓ⊔ r ℓ⊔ ℓ) where
  constructor property
  field
    ∥_∥-prop : ∀ {xs} → isProp (P xs)
    ∥_∥_&_∷_⟨_⟩ : (p : 𝑅) → (x : A) → (xs : W A) → P xs → P (p & x ∷ xs)
    ∥_∥[] : P []
  private z = ∥_∥[]; f = ∥_∥_&_∷_⟨_⟩
  ∥_∥⇑ = elim
          (λ {xs} → isProp→isSet (∥_∥-prop {xs}))
          f z
          (λ p q x xs pxs → toPathP (∥_∥-prop (transp (λ i → P (dup p q x xs i)) i0 (f p x (q & x ∷ xs) (f q x xs pxs))) (f (p + q) x xs pxs) ))
          (λ p x q y xs pxs → toPathP (∥_∥-prop (transp (λ i → P (com p x q y xs i)) i0 (f p x (q & y ∷ xs) (f q y xs pxs))) (f q y (p & x ∷ xs) (f p x xs pxs))))
          λ x xs pxs → toPathP (∥_∥-prop (transp (λ i → P (del x xs i)) i0 (f 0# x xs pxs)) pxs)
  ∥_∥⇓ = run ∥_∥⇑
  {-# INLINE ∥_∥⇑ #-}
  {-# INLINE ∥_∥⇓ #-}
open Property public

infixr 1 Property

syntax Property A (λ v → e) = W-ψ[ v ⦂ A ] e

record EqualityProof {B : Type b} (A : Type a) (P : W A → AnEquality B) : Type (a ℓ⊔ b ℓ⊔ ℓ) where
  Pr : W A → Type (b ℓ⊔ ℓ)
  Pr xs = let e = P xs in lhs e ≡ rhs e

  field
    ⟦_⟧≡_&_∷_⟨_⟩ : (p : 𝑅) → (x : A) → (xs : W A) → Pr xs → Pr (p & x ∷ xs)
    ⟦_⟧≡[] : Pr []

  _⇑≡ : Eliminator A Pr
  _⇑≡ = ∥ property (trunc _ _) ⟦_⟧≡_&_∷_⟨_⟩ ⟦_⟧≡[] ∥⇑

  _⇓≡_ : (xs : W A) → Pr xs
  _⇓≡_ = run _⇑≡
  {-# INLINE _⇑≡ #-}
  {-# INLINE _⇓≡_ #-}
open EqualityProof public

infixr 1 EqualityProof
syntax EqualityProof A (λ v → e) = W-ψ[ v ⦂ A ]≡ e
