{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Data.RecursionSchemes where

open import Function
open import Data.Sum
open import Data.Sigma.Base
open import Level
open import Data.Unit

data Functor : Type₀ where
  U I P : Functor
  _⊕_ _⊗_ : (F G : Functor) → Functor
  _⊚_ : (F G : Functor) → Functor

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
  ⟦ F ⊚ G ⟧ A R = μ F (⟦ G ⟧ A R)

  data μ (F : Functor) (A : Type₀) : Type₀  where
    ⟨_⟩ : ⟦ F ⟧ A (μ F A) → μ F A

record Wrap (A : Type₀) : Type₀  where
  constructor wrap
  field unwrap : A
open Wrap

mapμ : (A → B) → μ F A → μ F B
mapμ f ⟨ x ⟩ = ⟨ go _ f (wrap x) ⟩
  where
  go : ∀ G → (A → B) → Wrap (⟦ G ⟧ A (μ F A)) → ⟦ G ⟧ B (μ F B)
  go U         f xs = tt
  go I         f (wrap (recur xs)) = recur (mapμ f xs)
  go P         f (wrap (param xs)) = param (f xs)
  go (G₁ ⊕ G₂) f (wrap (inl x)) = inl (go G₁ f (wrap x))
  go (G₁ ⊕ G₂) f (wrap (inr x)) = inr (go G₂ f (wrap x))
  go (G₁ ⊗ G₂) f (wrap (x , y)) = go G₁ f (wrap x) , go G₂ f (wrap y)
  go (G₁ ⊚ G₂) f (wrap xs) = {!!} -- mapμ (go G₂ f ∘′ wrap) xs

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
  go F (G₁ ⊚ G₂) g f (wrap xs) = {!!} -- mapμ (go F G₂ g f ∘′ wrap) xs
