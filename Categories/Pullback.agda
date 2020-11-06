{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Categories

module Categories.Pullback {ℓ₁ ℓ₂} (C : Category ℓ₁ ℓ₂) where

open Category C

record Pullback (f : X ⟶ Z) (g : Y ⟶ Z) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  field
    {P} : Ob
    p₁ : P ⟶ X
    p₂ : P ⟶ Y
    commute : f · p₁ ≡ g · p₂
    ump : ∀ {A : Ob} (h₁ : A ⟶ X) (h₂ : A ⟶ Y) → f · h₁ ≡ g · h₂ →
              ∃![ u ] ((p₁ · u ≡ h₁) × (p₂ · u ≡ h₂))


HasPullbacks : Type (ℓ₁ ℓ⊔ ℓ₂)
HasPullbacks = ∀ {X Y Z} (f : X ⟶ Z) (g : Y ⟶ Z) → Pullback f g
