{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.All.Def where

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

dup-◻ : (P : A → Type p) → (x : A) (xs : Type p) → (∥ P x ∥ × ∥ P x ∥ × xs) ⇔ (∥ P x ∥ × xs)
dup-◻ P _ _ .fun = snd
dup-◻ P _ _ .inv (x , xs) = x , x , xs
dup-◻ P _ _ .rightInv (x , xs) = refl
dup-◻ P _ _ .leftInv  (x₁ , x₂ , xs) i .fst = squash x₂ x₁ i
dup-◻ P _ _ .leftInv  (x₁ , x₂ , xs) i .snd = (x₂ , xs)

com-◻ : (P : A → Type p) → (x y : A) (xs : Type p) → (∥ P x ∥ × ∥ P y ∥ × xs) ⇔ (∥ P y ∥ × ∥ P x ∥ × xs)
com-◻ P _ _ _ .fun (x , y , xs) = y , x , xs
com-◻ P _ _ _ .inv (y , x , xs) = x , y , xs
com-◻ P _ _ _ .leftInv  (x , y , xs) = refl
com-◻ P _ _ _ .rightInv (x , y , xs) = refl

◻′ : (P : A → Type p) → A ↘ hProp p
[ ◻′ P ]-set = isSetHProp
([ ◻′ P ] x ∷ (xs , hxs)) .fst = ∥ P x ∥ × xs
([ ◻′ P ] x ∷ (xs , hxs)) .snd y z = ΣProp≡ (λ _  → hxs) (squash (fst y) (fst z))
[ ◻′ P ][] = ⊤ , λ x y _ → x
[ ◻′ P ]-dup x xs = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (dup-◻ P x (xs .fst)))
[ ◻′ P ]-com x y xs = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (com-◻ P x y (xs .fst)))

◻ : (P : A → Type p) → 𝒦 A → Type p
◻ P xs = [ ◻′ P ]↓ xs .fst

isProp-◻ : ∀ {P : A → Type p} {xs} → isProp (◻ P xs)
isProp-◻ {P = P} {xs = xs} = [ ◻′ P ]↓ xs .snd
