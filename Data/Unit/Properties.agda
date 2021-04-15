{-# OPTIONS --cubical --safe #-}

module Data.Unit.Properties where

open import Data.Unit
open import Level
open import HLevels

isProp⊤ : isProp ⊤
isProp⊤ _ _ i = tt
