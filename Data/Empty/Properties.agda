{-# OPTIONS --cubical --safe #-}

module Data.Empty.Properties where

open import Data.Empty.Base
open import Level
open import HLevels

isProp⊥ : isProp ⊥
isProp⊥ ()

isProp¬ : (A : Type a) → isProp (¬ A)
isProp¬ _ f g i x = isProp⊥ (f x) (g x) i

