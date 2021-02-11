{-# OPTIONS --cubical --safe #-}

module Control.Monad.Levels.Definition where

open import Prelude
open import Data.Bag

data Levels (A : Type a) : Type a where
  _∷_ : ⟅ A ⟆ → Levels A → Levels A
  []  : Levels A

  trail : [] ∷ [] ≡ []
  trunc : isSet (Levels A)
