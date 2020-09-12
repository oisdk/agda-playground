{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Properties where

open import Prelude hiding (⊥; ⊤)
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Definition
open import Cubical.Foundations.HLevels
open import Data.Empty.UniversePolymorphic
open import HITs.PropositionalTruncation.Sugar
open import HITs.PropositionalTruncation.Properties
open import HITs.PropositionalTruncation
open import Data.Unit.UniversePolymorphic
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Def
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Decidable.Logic

private
  variable p : Level

P∃◇ : ∀ {p} {P : A → Type p} → ∀ xs → ◇ P xs → ∥ ∃ P ∥
P∃◇ {A = A} {P = P} = ∥ P∃◇′ ∥⇓
  where
  P∃◇′ : xs ∈𝒦 A ⇒∥ (◇ P xs → ∥ ∃ P ∥) ∥
  ∥ P∃◇′ ∥-prop p q i ◇Pxs = squash (p ◇Pxs) (q ◇Pxs) i
  ∥ P∃◇′ ∥[] ()
  ∥ P∃◇′ ∥ x ∷ xs ⟨ Pxs ⟩ ◇Pxs =
    ◇Pxs >>=
      either′
        (λ Px → ∣ x , Px ∣ )
        (λ ◇Pxxs → Pxs ◇Pxxs)
