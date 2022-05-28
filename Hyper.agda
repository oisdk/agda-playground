{-# OPTIONS --cubical --no-termination-check --no-positivity-check #-}

module Hyper where

open import Prelude

infixr 0 _↬_
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive; constructor ⟪_⟫
  infixl 2 _·_
  field
    _·_ : B ↬ A → B
open _↬_

𝕀 : A ↬ A
𝕀 · x = x · 𝕀

cata : (((C → A) → B) → C) → A ↬ B → C
cata ϕ h = ϕ λ k → h · ⟪ k ∘ cata ϕ ⟫

ana : (C → (C → A) → B) → C → A ↬ B
ana ψ r · x = ψ r λ y → x · ana ψ y

_◂_ : (B → C) → A ↬ B → A ↬ C
_◂_ f = ana λ h k → f (h · ⟪ k ⟫)

_▸_ : (B ↬ C) → (A → B) → A ↬ C
h ▸ f = ana (λ h k → h · ⟪ f ∘ k ⟫) h

