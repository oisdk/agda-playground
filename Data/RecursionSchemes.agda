{-# OPTIONS --without-K #-}

module Data.RecursionSchemes where

open import Function
open import Data.Sum
open import Data.Sigma.Base
open import Level
open import Data.Unit
open import Data.List.Base using (List; _∷_; []; foldr; foldl)

data Functor : Type₀ where
  U I P : Functor
  _⊕_ _⊗_ : (F G : Functor) → Functor
  _⊚_ : (F G : Functor) → Functor

variable
  F G : Functor
  Fs : List Functor
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

comps : List (Functor × Functor) → Type₀ → Type₀
comps xs A = foldr (λ { (F , G) A → ⟦ F ⟧ A (μ G A) }) A xs

go : ∀ Gs → (A → B) → Wrap (comps Gs A) → comps Gs B
go [] f (wrap xs) = f xs
go ((U       , F) ∷ Fs) f xs = tt
go ((G₁ ⊕ G₂ , F) ∷ Fs) f (wrap (inl x)) = inl (go ((G₁ , F) ∷ Fs) f (wrap x))
go ((G₁ ⊕ G₂ , F) ∷ Fs) f (wrap (inr x)) = inr (go ((G₂ , F) ∷ Fs) f (wrap x))
go ((G₁ ⊗ G₂ , F) ∷ Fs) f (wrap (x , y)) = go ((G₁ , F) ∷ Fs) f (wrap x) , go ((G₂ , F) ∷ Fs) f (wrap y)
go ((P       , F) ∷ Fs) f (wrap (param xs)) = param (go Fs f (wrap xs))
go ((I       , F) ∷ Fs) f (wrap (recur ⟨ xs ⟩)) = recur ⟨ go ((F , F) ∷ Fs) f (wrap xs) ⟩
go ((G₁ ⊚ G₂ , F) ∷ Fs) f (wrap ⟨ xs ⟩) = ⟨ go ((G₁ , G₁) ∷ (G₂ , F) ∷ Fs) f (wrap xs) ⟩

mapμ : (A → B) → μ F A → μ F B
mapμ {F = F} f ⟨ xs ⟩ = ⟨ go ((F , F) ∷ []) f (wrap xs) ⟩

