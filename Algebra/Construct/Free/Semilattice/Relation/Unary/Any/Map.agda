{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Map where

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
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Membership

private
  variable p : Level
  variable P : A → Type p

-- map-◇-fn : ∀ x → P x → ∀ y xs → (x ∈ xs → ◇ P xs) → (y ≡ x) ⊎ (x ∈ xs) → ◇ P (y ∷ xs)
-- map-◇-fn {P = P} x Px y xs k (inl y≡x) = ∣ inl (subst P (sym y≡x) Px) ∣
-- map-◇-fn x Px y xs k (inr x∈xs) = ∣ inr (k x∈xs) ∣

-- map-◇-prop : ∀ (x : A) {xs} → isProp (x ∈ xs → ◇ P xs)
-- map-◇-prop {P = P} x {xs} p q i x∈xs = ◇′ P xs .snd (p x∈xs) (q x∈xs) i

-- map-◇ : ∀ (x : A) → P x → (xs : 𝒦 A) → x ∈ xs → ◇ P xs
-- map-◇ {A = A} {P = P} x Px =
--   𝒦-elim-prop {A = A} {P = λ ys → x ∈ ys → ◇ P ys}
--     (map-◇-prop {A = A} {P = P} x)
--     (λ y xs Pxs → recPropTrunc squash (map-◇-fn x Px y xs Pxs))
--     (λ ())
