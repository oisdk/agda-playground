{-# OPTIONS --cubical --safe #-}

module Container.Stream where

open import Prelude
open import Data.Fin
open import Container

Stream : Type a → Type a
Stream = ⟦ ⊤ , const ℕ ⟧
