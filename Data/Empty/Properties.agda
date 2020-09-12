{-# OPTIONS --cubical --safe #-}

module Data.Empty.Properties where

open import Data.Empty.Base
open import Cubical.Data.Empty using (isProp⊥) public
open import Level
open import HLevels

isProp¬ : (A : Type a) → isProp (¬ A)
isProp¬ _ f g i x = isProp⊥ (f x) (g x) i
