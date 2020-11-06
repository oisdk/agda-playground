{-# OPTIONS --cubical --safe #-}

open import Prelude hiding (A; B)
open import Categories

module Categories.Pushout {ℓ₁ ℓ₂} (C : Category ℓ₁ ℓ₂) where

open Category C

private
  variable
    A B : Ob
    h₁ h₂ j : A ⟶ B

record Pushout (f : X ⟶ Y) (g : X ⟶ Z) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  field
    {Q} : Ob
    i₁ : Y ⟶ Q
    i₂ : Z ⟶ Q
    commute : i₁ · f ≡ i₂ · g
    universal : h₁ · f ≡ h₂ · g → Q ⟶ Codomain h₁
    unique : ∀ {eq : h₁ · f ≡ h₂ · g} →
             j · i₁ ≡ h₁ → j · i₂ ≡ h₂ →
             j ≡ universal eq

    universal·i₁≡h₁  : ∀ {eq : h₁ · f ≡ h₂ · g} →
                         universal eq · i₁ ≡ h₁
    universal·i₂≡h₂  : ∀ {eq : h₁ · f ≡ h₂ · g} →
                         universal eq · i₂ ≡ h₂

HasPushouts : Type (ℓ₁ ℓ⊔ ℓ₂)
HasPushouts = ∀ {X Y Z} → (f : X ⟶ Y) → (g : X ⟶ Z) → Pushout f g
