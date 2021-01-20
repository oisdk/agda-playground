{-# OPTIONS --cubical #-}

module Data.RecursionSchemes where

open import Prelude hiding (I)

data Functor : Type₀ where
  U I P : Functor
  _⊕_ _⊗_ : (F G : Functor) → Functor
  -- _⊚_ : (F G : Functor) → Functor

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
  ⟦_⟧ : Functor → Type₀ → Type₀ → Type₀
  ⟦ U     ⟧ A R = ⊤
  ⟦ I     ⟧ A R = Recur R
  ⟦ P     ⟧ A R = Param A
  ⟦ F ⊕ G ⟧ A R = ⟦ F ⟧ A R ⊎ ⟦ G ⟧ A R
  ⟦ F ⊗ G ⟧ A R = ⟦ F ⟧ A R × ⟦ G ⟧ A R
  -- ⟦ F ⊚ G ⟧ A R = μ F (⟦ G ⟧ A R)

  data μ (F : Functor) (A : Type₀) : Type₀  where
    ⟨_⟩ : ⟦ F ⟧ A (μ F A) → μ F A

record Wrap (A : Type₀) : Type₀  where
  constructor wrap
  field unwrap : A
open Wrap

cata : (⟦ F ⟧ A R → R) → μ F A → R
cata alg ⟨ x ⟩ = alg (go _ _ id alg (wrap x))
  where
  go : ∀ F G → (A → B) → (⟦ F ⟧ A R → R) → Wrap (⟦ G ⟧ A (μ F A)) → ⟦ G ⟧ B R
  go F U         g _ xs = tt
  go F I         g f (wrap (recur xs)) = recur (cata f xs)
  go F P         g f (wrap (param xs)) = param (g xs)
  go F (G₁ ⊕ G₂) g f (wrap (inl x)) = inl (go F G₁ g f (wrap x))
  go F (G₁ ⊕ G₂) g f (wrap (inr x)) = inr (go F G₂ g f (wrap x))
  go F (G₁ ⊗ G₂) g f (wrap (x , y)) = go F G₁ g f (wrap x) , go F G₂ g f (wrap y)

