{-# OPTIONS --cubical #-}

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

map : (A → B) → ⟦ F ⟧ A → ⟦ F ⟧ B
map {F = U}     f x = tt
map {F = I}     f (recur x) = recur (f x)
map {F = F ⊕ G} f (inl x) = inl (map f x)
map {F = F ⊕ G} f (inr x) = inr (map f x)
map {F = F ⊗ G} f (x , y) = map f x , map f y

module NonStructuralTermCata where
  {-# TERMINATING #-}
  cata : (⟦ F ⟧ A → A) → μ F → A
  cata alg ⟨ x ⟩ = alg (map (cata alg) x)

mutual
  cata : (⟦ F ⟧ A → A) → μ F → A
  cata f ⟨ x ⟩ = f (catamap _ _ f (wrap x))

  catamap : ∀ F G → (f : ⟦ F ⟧ A → A) → Wrap (⟦ G ⟧ (μ F)) → ⟦ G ⟧ A
  catamap F U         f x = tt
  catamap F (G₁ ⊕ G₂) f (wrap (inl x)) = inl (catamap F G₁ f (wrap x))
  catamap F (G₁ ⊕ G₂) f (wrap (inr x)) = inr (catamap F G₂ f (wrap x))
  catamap F (G₁ ⊗ G₂) f (wrap (x , y)) = catamap F G₁ f (wrap x) , catamap F G₂ f (wrap y)
  catamap F I         f (wrap (recur x)) = recur (cata f x)

