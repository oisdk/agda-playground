{-# OPTIONS --cubical --safe --guardedness #-}

module Container.Fixpoint where

open import Container
open import Prelude

data μ (C : Container) : Type where
  sup : ⟦ C ⟧ (μ C) → μ C

record ν (C : Container ) : Type where
  coinductive
  field inf : ⟦ C ⟧ (ν C)
open ν public
