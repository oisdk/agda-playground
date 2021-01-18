{-# OPTIONS --cubical --safe #-}

module Container.Fixpoint where

open import Container
open import Prelude

data μ {s p} (C : Container s p) : Type (s ℓ⊔ p) where
  sup : ⟦ C ⟧ (μ C) → μ C

record ν {s p} (C : Container s p) : Type (s ℓ⊔ p) where
  coinductive
  field inf : ⟦ C ⟧ (ν C)
open ν public
