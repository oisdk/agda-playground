{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Categories

module Categories.Coequalizer {ℓ₁ ℓ₂} (C : Category ℓ₁ ℓ₂) where

open Category C


private
  variable
    h i : X ⟶ Y

record Coequalizer (f g : X ⟶ Y) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  field
    {obj} : Ob
    arr   : Y ⟶ obj

    equality   : arr · f ≡ arr · g
    coequalize : ∀ {H} {h : Y ⟶ H} → h · f ≡ h · g → obj ⟶ H
    universal  : ∀ {H} {h : Y ⟶ H} {eq : h · f ≡ h · g} → h ≡ coequalize eq · arr
    unique     : ∀ {H} {h : Y ⟶ H} {i : obj ⟶ H} {eq : h · f ≡ h · g} → h ≡ i · arr → i ≡ coequalize eq
