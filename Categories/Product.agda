{-# OPTIONS --cubical --safe #-}

module Categories.Product where

open import Prelude hiding (_×_)
open import Categories

module _ {ℓ₁ ℓ₂} (C : Category ℓ₁ ℓ₂) where
  open Category C

  module _ (X Y : Ob) where
    record Product : Type (ℓ₁ ℓ⊔ ℓ₂) where
      field
        obj : Ob
        proj₁ : C [ obj , X ]
        proj₂ : C [ obj , Y ]
        ump : (f : C [ Z , X ]) (g : C [ Z , Y ]) →
              ∃![ f×g ] ((C [ proj₁ ∘ f×g ] ≡ f) Prelude.× (C [ proj₂ ∘ f×g ] ≡ g))
      _P[_×_] : ∀ {Z} → (π₁ : C [ Z , X ]) (π₂ : C [ Z , Y ]) →
                C [ Z , obj ]
      _P[_×_] π₁ π₂ = fst (ump π₁ π₂)

  record HasProducts : Type (ℓ₁ ℓ⊔ ℓ₂) where
    field product : (X Y : Ob) → Product X Y

    _×_ : Ob → Ob → Ob
    A × B = Product.obj (product A B)

    module _ {A A′ B B′ : Ob} where
      open Product using (_P[_×_])
      open Product (product A B) hiding (_P[_×_])

      _|×|_ : C [ A , A′ ] → C [ B , B′ ] → C [ Product.obj (product A B) , Product.obj (product A′ B′) ]
      f |×| g = product A′ B′ P[ C [ f ∘ proj₁ ] × C [ g ∘ proj₂ ] ]
