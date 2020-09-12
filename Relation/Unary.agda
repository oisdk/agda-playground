{-# OPTIONS --cubical --safe #-}

module Relation.Unary where

open import Relation.Nullary.Decidable
open import Level
open import Path

Decidable : (A → Type b) → Type _
Decidable P = ∀ x → Dec (P x)

AtMostOne : (A → Type b) → Type _
AtMostOne P = ∀ x y → P x → P y → x ≡ y
