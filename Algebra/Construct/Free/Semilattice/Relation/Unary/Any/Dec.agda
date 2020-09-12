{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Dec where

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

◇? : ∀ {P : A → Type p} → (∀ x → Dec (P x)) → (xs : 𝒦 A) → Dec (◇ P xs)
◇? {A = A} {P = P} P? = 𝒦-elim-prop (λ {xs} → isPropDec (isProp-◇ {P = P} {xs = xs})) (λ x xs → fn x xs (P? x)) (no (Poly⊥⇔Mono⊥ .fun))
  where
  fn : ∀ x xs → Dec (P x) → Dec (◇ P xs) → Dec (◇ P (x ∷ xs))
  fn x xs (yes Px) Pxs = yes ∣ inl Px ∣
  fn x xs (no ¬Px) (yes Pxs) = yes ∣ inr Pxs ∣
  fn x xs (no ¬Px) (no ¬Pxs) = no (refute-trunc (either′ ¬Px ¬Pxs))
