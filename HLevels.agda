{-# OPTIONS --cubical --safe #-}

module HLevels where

open import Path
open import Cubical.Foundations.Everything
  using (isProp
        ;isSet
        ;isContr
        ;isPropIsContr
        ;isProp→isSet
        ;isOfHLevel→isOfHLevelDep
        ;hProp
        ;isSetHProp
        ;isPropIsProp
        )
  public

open import Level
open import Data.Sigma

hSet : ∀ ℓ → Type (ℓsuc ℓ)
hSet ℓ = Σ (Type ℓ) isSet
