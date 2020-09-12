{-# OPTIONS --cubical --safe #-}

module Container.List where

open import Prelude
open import Data.Fin
open import Container

List : Type a → Type a
List = ⟦ ℕ , Fin ⟧
