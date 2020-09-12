{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Decidable.Properties where

open import Relation.Nullary.Decidable.Base
open import Level
open import Relation.Nullary.Stable.Base
open import Data.Empty
open import HLevels
open import Data.Empty.Properties using (isProp¬)
open import Data.Unit
open import Data.Empty

Dec→DoubleNegElim : (A : Type a) → Dec A → ¬ ¬ A → A
Dec→DoubleNegElim A (yes p)  _       = p
Dec→DoubleNegElim A (no ¬p)  contra  = ⊥-elim (contra ¬p)

Dec→Stable : ∀ {ℓ} (A : Type ℓ) → Dec A → Stable A
Dec→Stable A (yes x) = λ _ → x
Dec→Stable A (no x) = λ f → ⊥-elim (f x)

isPropDec : (Aprop : isProp A) → isProp (Dec A)
isPropDec Aprop (yes a) (yes a') i = yes (Aprop a a' i)
isPropDec Aprop (yes a) (no ¬a) = ⊥-elim (¬a a)
isPropDec Aprop (no ¬a) (yes a) = ⊥-elim (¬a a)
isPropDec {A = A} Aprop (no ¬a) (no ¬a') i = no (isProp¬ A ¬a ¬a' i)

True : Dec A → Type₀
True (yes _) = ⊤
True (no  _) = ⊥

toWitness : {x : Dec A} → True x → A
toWitness {x = yes p} _ = p
