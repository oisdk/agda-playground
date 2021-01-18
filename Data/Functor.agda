{-# OPTIONS --cubical --safe #-}

module Data.Functor where

open import Prelude

record Functor ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    F : Type ℓ₁ → Type ℓ₂
    map : (A → B) → F A → F B

    identity : map {A = A} id ≡ id
    compose : (f : B → C) (g : A → B) → map (f ∘ g) ≡ map f ∘ map g
