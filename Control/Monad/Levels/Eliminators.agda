{-# OPTIONS --cubical --safe #-}

module Control.Monad.Levels.Eliminators where

open import Prelude
open import Data.Bag
open import Control.Monad.Levels.Definition

record Eliminator {a p} (A : Type a) (P : Levels A → Type p) : Type (a ℓ⊔ p) where
  constructor elim
  field
    ⟦_⟧-set : ∀ {xs} → isSet (P xs)
    ⟦_⟧_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
    ⟦_⟧[] : P []
    ⟦_⟧-trail : PathP (λ i → P (trail i)) (⟦_⟧_∷_⟨_⟩ [] [] ⟦_⟧[]) ⟦_⟧[]

  run : ∀ xs → P xs
  run (x ∷ xs) = ⟦_⟧_∷_⟨_⟩ x xs (run xs)
  run [] = ⟦_⟧[]
  run (trail i) = ⟦_⟧-trail i
  run (trunc xs ys x y i j) =
    isOfHLevel→isOfHLevelDep 2
      (λ xs → ⟦_⟧-set {xs})
      (run xs) (run ys)
      (cong run x) (cong run y)
      (trunc xs ys x y)
      i j

  _⇓_ : (xs : Levels A) → P xs
  _⇓_ = run
  {-# INLINE _⇓_ #-}
open Eliminator public
infixr 1 Eliminator

syntax Eliminator A (λ v → e) = Levels-Π[ v ⦂ e ] A

record Recursor (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor rec
  field
    [_]-set : isSet B
    [_]_∷_⟨_⟩ : (x : ⟅ A ⟆) → (xs : Levels A) → B → B
    [_][] : B
  private f = [_]_∷_⟨_⟩; z = [_][]
  field
    [_]-trail : f [] [] z ≡ z

  _↑ : Eliminator A (λ _ → B)
  _↑ = elim [_]-set f z [_]-trail

  _↓_ : Levels A → B
  _↓_ = run _↑
  {-# INLINE _↑ #-}
  {-# INLINE _↓_ #-}
open Recursor public

infixr 1 Recursor

syntax Recursor A B = Levels-ϕ[ A ] B

infix 4 _⊜_
record AnEquality (A : Type a) : Type a where
  constructor _⊜_
  field lhs rhs : Levels A
open AnEquality public

record Property {r} (A : Type a) (P : Levels A → Type r) : Type (a ℓ⊔ r) where
  constructor property
  field
    ∥_∥-prop : ∀ {xs} → isProp (P xs)
    ∥_∥_∷_⟨_⟩ : (x : ⟅ A ⟆) → (xs : Levels A) → P xs → P (x ∷ xs)
    ∥_∥[] : P []
  private z = ∥_∥[]; f = ∥_∥_∷_⟨_⟩
  ∥_∥⇑ = elim
          (λ {xs} → isProp→isSet (∥_∥-prop {xs}))
          f z
          (toPathP (∥_∥-prop (transp (λ i → P (trail i)) i0 (f [] [] z)) z))
  ∥_∥⇓ = run ∥_∥⇑
  {-# INLINE ∥_∥⇑ #-}
  {-# INLINE ∥_∥⇓ #-}
open Property public

infixr 1 Property

syntax Property A (λ v → e) = Levels-ψ[ v ⦂ A ] e

record EqualityProof {B : Type b} (A : Type a) (P : Levels A → AnEquality B) : Type (a ℓ⊔ b) where
  Pr : Levels A → Type b
  Pr xs = let e = P xs in lhs e ≡ rhs e

  field
    ⟦_⟧≡_∷_⟨_⟩ : (x : ⟅ A ⟆) → (xs : Levels A) → Pr xs → Pr (x ∷ xs)
    ⟦_⟧≡[] : Pr []

  _⇑≡ : Eliminator A Pr
  _⇑≡ = ∥ property (trunc _ _) ⟦_⟧≡_∷_⟨_⟩ ⟦_⟧≡[] ∥⇑

  _⇓≡_ : (xs : Levels A) → Pr xs
  _⇓≡_ = run _⇑≡
  {-# INLINE _⇑≡ #-}
  {-# INLINE _⇓≡_ #-}
open EqualityProof public

infixr 1 EqualityProof
syntax EqualityProof A (λ v → e) = Levels-ψ[ v ⦂ A ]≡ e
