{-# OPTIONS --cubical --safe #-}

module Data.RecursionSchemes where

open import Prelude hiding (I)

data Functor : Type₀ where
  U I : Functor
  _⊕_ _⊗_ : (F G : Functor) → Functor

variable
  F G : Functor
  R S : Type₀

record Param (A : Type₀) : Type₀ where
  constructor param
  field getParam : A
open Param

record Recur (A : Type₀) : Type₀ where
  constructor recur
  field getRecur : A
open Recur

mutual
  ⟦_⟧ : Functor → Type₀ → Type₀
  ⟦ U ⟧ A = ⊤
  ⟦ I ⟧ A = Recur A
  ⟦ F ⊕ G ⟧ A = ⟦ F ⟧ A ⊎ ⟦ G ⟧ A
  ⟦ F ⊗ G ⟧ A = ⟦ F ⟧ A × ⟦ G ⟧ A


data μ (F : Functor) : Type₀  where
  ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

record Wrap (A : Type₀) : Type₀  where
  constructor wrap
  field unwrap : A
open Wrap

fmap : ∀ F G → (f : ⟦ F ⟧ A → A) → Wrap (⟦ G ⟧ (μ F)) → ⟦ G ⟧ A
cata : ∀ F   → (f : ⟦ F ⟧ A → A) → μ F → A

fmap F U         f x = tt
fmap F (G₁ ⊕ G₂) f (wrap (inl x)) = inl (fmap F G₁ f (wrap x))
fmap F (G₁ ⊕ G₂) f (wrap (inr x)) = inr (fmap F G₂ f (wrap x))
fmap F (G₁ ⊗ G₂) f (wrap (x , y)) = fmap F G₁ f (wrap x) , fmap F G₂ f (wrap y)
fmap F I         f (wrap (recur x)) = recur (cata F f x)

cata F f ⟨ x ⟩ = f (fmap F F f (wrap x))
