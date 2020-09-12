{-# OPTIONS --cubical --safe #-}

module Lens.Definition where

open import Prelude

record LensPart (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor lens-part
  field
    get : B
    set : B → A
open LensPart public

record Lens (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  field
    into : A → LensPart A B
    get-set : ∀ s v → into (into s .set v) .get ≡ v
    set-get : ∀ s → into s .set (into s .get) ≡ s
    set-set : ∀ s v₁ v₂ → into (into s .set v₁) .set v₂ ≡ into s .set v₂
open Lens public

