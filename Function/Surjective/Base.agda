{-# OPTIONS --cubical --safe #-}

module Function.Surjective.Base where

open import Path
open import Function.Fiber
open import Level
open import HITs.PropositionalTruncation
open import Data.Sigma

Surjective : (A → B) → Type _
Surjective f = ∀ y → ∥ fiber f y ∥

SplitSurjective : (A → B) → Type _
SplitSurjective f = ∀ y → fiber f y

infixr 0 _↠!_ _↠_

_↠!_ : Type a → Type b → Type (a ℓ⊔ b)
A ↠! B = Σ (A → B) SplitSurjective

_↠_ : Type a → Type b → Type (a ℓ⊔ b)
A ↠ B = Σ (A → B) Surjective
