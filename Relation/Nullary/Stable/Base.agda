{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Stable.Base where

open import Data.Empty
open import Level

Stable : Type a → Type a
Stable A = ¬ ¬ A → A
