{-# OPTIONS --cubical --safe #-}

module Categories.Functor where

open import Prelude
open import Categories

record Functor {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (C : PreCategory ℓ₁ ℓ₂) (D : PreCategory ℓ₃ ℓ₄) : Type (ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃ ℓ⊔ ℓ₄) where
  private module C = PreCategory C
  private module D = PreCategory D
  field
    F₀ : C.Ob → D.Ob
    F₁ : ∀ {X Y} → (X C.⟶ Y) → (F₀ X D.⟶ F₀ Y)

    identity : ∀ {X} → F₁ (C.Id {X}) ≡ D.Id
    homomorphism : ∀ {X Y Z} → (f : X C.⟶ Y) (g : Y C.⟶ Z) →
                   F₁ (g C.· f) ≡ F₁ g D.· F₁ f
