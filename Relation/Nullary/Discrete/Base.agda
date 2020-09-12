{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Discrete.Base where

open import Relation.Nullary.Decidable.Base
open import Path
open import Level

Discrete : Type a → Type a
Discrete A = (x y : A) → Dec (x ≡ y)
