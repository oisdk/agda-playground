{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Stable.Properties where

open import Data.Empty
open import Level
open import Relation.Nullary.Stable.Base
open import Path
open import HLevels
open import Data.Empty.Properties

open import Cubical.Foundations.Everything
  using (hcomp; _∧_; i0; i1)

Stable≡→isSet : ∀ {ℓ} {A : Type ℓ} → (st : ∀ (a b : A) → Stable (a ≡ b)) → isSet A
Stable≡→isSet {A = A} st a b p q j i =
  let f : (x : A) → a ≡ x → a ≡ x
      f x p = st a x (λ h → h p)
      fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
      fIsConst = λ x p q i → st a x (isProp¬ _ (λ h → h p) (λ h → h q) i)
      rem : (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
      rem p j = f (p j) (λ i → p (i ∧ j))
  in hcomp (λ k → λ { (i = i0) → f a refl k
                    ; (i = i1) → fIsConst b p q j k
                    ; (j = i0) → rem p i k
                    ; (j = i1) → rem q i k }) a
