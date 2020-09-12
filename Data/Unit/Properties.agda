{-# OPTIONS --cubical --safe #-}

module Data.Unit.Properties where

open import Data.Unit
open import Prelude

isProp⊤ : isProp ⊤
isProp⊤ _ _ = refl
