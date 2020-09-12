{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Def where

open import Prelude hiding (⊥; ⊤)
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Definition
open import Cubical.Foundations.HLevels
open import Data.Empty.UniversePolymorphic
open import HITs.PropositionalTruncation.Sugar
open import HITs.PropositionalTruncation.Properties
open import HITs.PropositionalTruncation
open import Data.Unit.UniversePolymorphic

private
  variable p : Level

dup-◇ : (P : A → Type p) → (x : A) (xs : Type p) → ∥ P x ⊎ ∥ P x ⊎ xs ∥ ∥ ⇔ ∥ P x ⊎ xs ∥
dup-◇ P x xs .inv p = ∣ inr p ∣
dup-◇ P x xs .fun ps = ps >>= either (∣_∣ ∘ inl) id
dup-◇ P x xs .leftInv p = squash _ p
dup-◇ P x xs .rightInv p = squash p _

swap-◇ : {x y xs : Type p} → ∥ x ⊎ ∥ y ⊎ xs ∥ ∥ → ∥ y ⊎ ∥ x ⊎ xs ∥ ∥
swap-◇ p = p >>= either′ (∣_∣ ∘ inr ∘ ∣_∣ ∘ inl) (mapʳ (∣_∣ ∘ inr) ∥$∥_)

com-◇ : (P : A → Type p) → (x y : A) (xs : Type p) → ∥ P x ⊎ ∥ P y ⊎ xs ∥ ∥ ⇔ ∥ P y ⊎ ∥ P x ⊎ xs ∥ ∥
com-◇ P y z xs .fun = swap-◇
com-◇ P y z xs .inv = swap-◇
com-◇ P y z xs .leftInv  p = squash _ p
com-◇ P y z xs .rightInv p = squash _ p

◇′ : (P : A → Type p) → 𝒦 A → hProp p
◇′ P =
  𝒦-rec
    isSetHProp
    (λ { x (xs , _) → ∥ P x ⊎ xs ∥ , squash })
    (⊥ , λ ())
    (λ x xs → ΣProp≡ (λ _ → isPropIsProp) (isoToPath (dup-◇ P x (xs .fst))))
    (λ x y xs → ΣProp≡ (λ _ → isPropIsProp) (isoToPath (com-◇ P x y (xs .fst))))
{-# INLINE ◇′ #-}

◇ : (P : A → Type p) → 𝒦 A → Type p
◇ P xs = ◇′ P xs .fst

isProp-◇ : ∀ {P : A → Type p} {xs} → isProp (◇ P xs)
isProp-◇ {P = P} {xs = xs} = ◇′ P xs .snd
