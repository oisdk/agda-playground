{-# OPTIONS --no-termination-check #-}

module Hyper.NonPositive where

open import Prelude

infixr 2 _↬_
{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor hyp; inductive
  field invoke : (B ↬ A) → B
open _↬_ public

_⊙_ : B ↬ C → A ↬ B → A ↬ C
(f ⊙ g) .invoke k = f .invoke (g ⊙ k)


𝕀 : A ↬ A
𝕀 .invoke k = k .invoke 𝕀

𝕂 : A ↬ B ↬ A
𝕂 .invoke x .invoke y = x .invoke 𝕂

⟦_⟧ : A → B ↬ A
⟦ x ⟧ .invoke _ = x

⟦_⇓⟧ : A ↬ A → A
⟦ h ⇓⟧ = h .invoke 𝕀

infixr 5 _◃_
_◃_ : (A → B) → A ↬ B → A ↬ B
(f ◃ h) .invoke k = f (k .invoke h)

△ : (A → B) → A ↬ B
△ f = f ◃ △ f

𝔹 : (B ↬ C) ↬ (A ↬ B) ↬ (A ↬ C)
𝔹 = △ (△ ∘ _⊙_)

-- ℂ : (A ↬ B )

