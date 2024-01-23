{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Categories
open import Categories.Functor

module Categories.Diagram
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  (J : PreCategory ℓ₁ ℓ₂)
  (C : PreCategory ℓ₃ ℓ₄)
  (D : Functor J C)
  where

private module J = PreCategory J
private module C = PreCategory C
private module D = Functor D

Cone : _
Cone = Σ[ c ⦂ C.Ob ]
     × Σ[ cⱼ ⦂ (∀ i → c C.⟶ D.F₀ i) ]
     × (∀ i j (α : i J.⟶ j) → D.F₁ α C.· cⱼ i ≡ cⱼ j)



