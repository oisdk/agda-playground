{-# OPTIONS --cubical --safe #-}

module Control.Monad.Levels.Mult where

open import Prelude
open import Control.Monad.Levels.Definition
open import Control.Monad.Levels.Eliminators
open import Control.Monad.Levels.Zipping
open import Data.Bag hiding (bind)
open import Path.Reasoning

open import Cubical.Foundations.HLevels using (isOfHLevelΠ)

bind-alg : (A → Levels B) → Levels-ϕ[ A ] Levels B
[ bind-alg f ]-set = trunc
[ bind-alg f ] x ∷ _ ⟨ xs ⟩ = zip (⟦ levels-cmon ⟧ trunc f x) ([] ∷ xs)
[ bind-alg f ][] = []
[ bind-alg f ]-trail = trail

bind : Levels A → (A → Levels B) → Levels B
bind xs f = bind-alg f ↓ xs
