{-# OPTIONS --cubical --safe #-}

module Data.List.Kleene.Relation.Unary where

open import Data.List.Kleene
open import Prelude
open import Data.Fin
open import Relation.Nullary

private
  variable
    p : Level

◇⁺ : ∀ {A : Type a} (P : A → Type p) → A ⁺ → Type _
◇⁺ P xs = ∃[ i ] P (xs !⁺ i)

◇⋆ : ∀ {A : Type a} (P : A → Type p) → A ⋆ → Type _
◇⋆ P xs = ∃[ i ] P (xs !⋆ i)

module Exists {a} {A : Type a} {p} (P : A → Type p) where
  push : ∀ {x xs} → ◇⋆ P xs → ◇⁺ P (x & xs)
  push (n , x∈xs) = (fs n , x∈xs)

  pull : ∀ {x xs} → ¬ P x → ◇⁺ P (x & xs) → ◇⋆ P xs
  pull ¬Px (f0  , p∈xs) = ⊥-elim (¬Px p∈xs)
  pull ¬Px (fs n , p∈xs) = (n , p∈xs)

◻⁺ : {A : Type a} (P : A → Type p) → A ⁺ → Type _
◻⁺ P xs = ∀ i → P (xs !⁺ i)

◻⋆ : {A : Type a} (P : A → Type p) → A ⋆ → Type _
◻⋆ P xs = ∀ i → P (xs !⋆ i)

module Forall {a} {A : Type a} {p} (P : A → Type p) where
  push⁺ : ∀ {x xs} → P x → ◻⋆ P xs → ◻⁺ P (x & xs)
  push⁺ px pxs f0 = px
  push⁺ px pxs (fs n) = pxs n
