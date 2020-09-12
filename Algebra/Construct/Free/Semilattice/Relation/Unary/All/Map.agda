{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.All.Map where

open import Prelude hiding (⊥; ⊤)
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Definition
open import Cubical.Foundations.HLevels
open import Data.Empty.UniversePolymorphic
open import HITs.PropositionalTruncation.Sugar
open import HITs.PropositionalTruncation.Properties
open import HITs.PropositionalTruncation
open import Data.Unit.UniversePolymorphic
open import Algebra.Construct.Free.Semilattice.Relation.Unary.All.Def

private
  variable p : Level

map-◻ : ∀ {p} {P : A → Type p} → (∀ x → P x) → ∀ xs → ◻ P xs
map-◻ {A = A} {P = P} = λ f → ∥ map-◻′ f ∥⇓
  where
  map-◻′ : (∀ x → P x) → xs ∈𝒦 A ⇒∥ ◻ P xs ∥
  ∥ map-◻′ f ∥-prop {xs} = isProp-◻ {P = P} {xs = xs}
  ∥ map-◻′ f ∥[] = tt
  ∥ map-◻′ f ∥ x ∷ xs ⟨ Pxs ⟩ = ∣ f x ∣ , Pxs
