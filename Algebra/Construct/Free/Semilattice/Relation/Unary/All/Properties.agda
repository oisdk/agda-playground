{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.All.Properties where

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
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Membership
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Decidable.Logic

private
  variable p : Level

P∈◇ : ∀ {p} {P : A → Type p} → ∀ x xs → x ∈ xs → ◻ P xs → ∥ P x ∥
P∈◇ {A = A} {P = P} = λ x → ∥ P∈◇′ x ∥⇓
  where
  P∈◇′ : (x : A) → xs ∈𝒦 A ⇒∥ (x ∈ xs → ◻ P xs → ∥ P x ∥) ∥
  ∥ P∈◇′ x ∥-prop p q i x∈xs ◻Pxs = squash (p x∈xs ◻Pxs) (q x∈xs ◻Pxs) i
  ∥ P∈◇′ x ∥[] ()
  ∥ P∈◇′ x ∥ y ∷ ys ⟨ Pys ⟩ x∈xs ◻Pxs =
    x∈xs >>=
      either′
        (λ y≡x → subst (∥_∥ ∘ P) y≡x (◻Pxs .fst))
        (λ x∈ys → Pys x∈ys (◻Pxs .snd))
