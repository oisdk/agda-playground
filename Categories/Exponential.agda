{-# OPTIONS --cubical --safe #-}

module Categories.Exponential where

open import Prelude hiding (_×_)
open import Categories
open import Categories.Product

module _ {ℓ₁ ℓ₂} (C : Category ℓ₁ ℓ₂) (hasProducts : HasProducts C) where
  open Category C
  open HasProducts hasProducts

  module _ (Y Z : Ob) where
    record Exponential : Type (ℓ₁ ℓ⊔ ℓ₂) where
      field
        obj : Ob
        eval : C [ obj × Y , Z ]
        uniq : ∀ (X : Ob) (f : C [ X × Y , Z ]) →
              ∃![ f~ ] (C [ eval ∘ (f~ |×| Category.Id C) ] ≡ f)

  HasExponentials : Type (ℓ₁ ℓ⊔ ℓ₂)
  HasExponentials = ∀ X Y → Exponential X Y
