{-# OPTIONS --cubical --safe #-}

module HLevels where

open import Path
open import Cubical.Foundations.Prelude
  using (isProp
        ;isSet
        ;isContr
        ;isPropIsContr
        ;isProp→isSet
        ;isPropIsProp
        )
  public

open import Cubical.Foundations.HLevels
  using (isOfHLevel→isOfHLevelDep
        ;hProp
        ;isSetHProp
        ;hSet
        ;isPropΠ
        ;isSetΠ
        )
  public

open import Level
open import Data.Sigma

-- hSet : ∀ ℓ → Type (ℓsuc ℓ)
-- hSet ℓ = Σ (Type ℓ) isSet
