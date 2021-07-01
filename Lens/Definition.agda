{-# OPTIONS --cubical --safe #-}

module Lens.Definition where

open import Prelude

record LensPart (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor lens-part
  eta-equality
  field
    get : B
    set : B → A
open LensPart public

map-lens-part : LensPart A C → (A → B) → LensPart B C
get (map-lens-part xs f) = get xs
set (map-lens-part xs f) x = f (set xs x)

record LensLaws {A : Type a} {B : Type b} (into : A → LensPart A B) : Type (a ℓ⊔ b) where
  no-eta-equality
  field
    get-set : ∀ s v → into (into s .set v) .get ≡ v
    set-get : ∀ s → into s .set (into s .get) ≡ s
    set-set : ∀ s v₁ v₂ → into (into s .set v₁) .set v₂ ≡ into s .set v₂
open LensLaws public

Lens : Type a → Type b → Type (a ℓ⊔ b)
Lens A B = Σ (A → LensPart A B) LensLaws
