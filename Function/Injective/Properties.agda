{-# OPTIONS --cubical --safe #-}

module Function.Injective.Properties where

open import Level
open import Path
open import Data.Sigma
open import Function.Injective.Base
open import Relation.Nullary.Decidable
open import Relation.Nullary.Discrete
open import Function

Discrete-pull-inj : A ↣ B → Discrete B → Discrete A
Discrete-pull-inj (f , inj) _≟_ x y =
  case (f x ≟ f y) of
    λ  { (no ¬p) → no (¬p ∘ cong f)
       ; (yes p) → yes (inj x y p) }
