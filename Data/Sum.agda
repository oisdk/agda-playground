{-# OPTIONS --cubical --safe #-}

module Data.Sum where

open import Level
open import Cubical.Data.Sum using (_⊎_; inl; inr) public
open import Data.Bool using (Bool; true; false)
open import Function using (const)

either : ∀ {ℓ} {C : A ⊎ B → Type ℓ} →  ((a : A) → C (inl a)) → ((b : B) → C (inr b))
        → (x : A ⊎ B) → C x
either f _ (inl x) = f x
either _ g (inr y) = g y

⟦l_,r_⟧ = either

either′ : (A → C) → (B → C) → (A ⊎ B) → C
either′ = either

is-l : A ⊎ B → Bool
is-l = either′ (const true) (const false)

map-⊎ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Type a₁} {A₂ : Type a₂} {B₁ : Type b₁} {B₂ : Type b₂} →
      (A₁ → A₂) →
      (B₁ → B₂) →
      (A₁ ⊎ B₁) →
      (A₂ ⊎ B₂)
map-⊎ f g (inl x) = inl (f x)
map-⊎ f g (inr x) = inr (g x)

mapˡ : (A → B) → A ⊎ C → B ⊎ C
mapˡ f (inl x) = inl (f x)
mapˡ f (inr x) = inr x

mapʳ : (A → B) → C ⊎ A → C ⊎ B
mapʳ f (inl x) = inl x
mapʳ f (inr x) = inr (f x)
