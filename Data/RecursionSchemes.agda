{-# OPTIONS --cubical --safe #-}

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

comp : (Functor × Functor) → Type₀ → Type₀
comp (F , G) A = ⟦ F ⟧ A (μ G A)

comps : List (Functor × Functor) → Type₀ → Type₀
comps xs A = foldr comp A xs

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

ucomp : (Functor × Functor) → (Type₀ × Type₀) → (Type₀ × Type₀)
ucomp (G , F) (A , mA) = let B = ⟦ F ⟧ A mA in B , μ G B

ucomps : List (Functor × Functor) → (Type₀ × Type₀) → (Type₀ × Type₀)
ucomps  = flip (foldr ucomp)

fmap : ∀ G Gs → (⟦ F ⟧ A R → R) → Wrap (uncurry ⟦ G ⟧ (ucomps Gs (A , μ F A))) → uncurry ⟦ G ⟧ (ucomps Gs (A , R))
fmap (U      ) Fs f xs = tt
fmap (G₁ ⊕ G₂) Fs f (wrap (inl x)) = inl (fmap G₁ Fs f (wrap x))
fmap (G₁ ⊕ G₂) Fs f (wrap (inr x)) = inr (fmap G₂ Fs f (wrap x))
fmap (G₁ ⊗ G₂) Fs f (wrap (x , y)) = fmap G₁ Fs f (wrap x) , fmap G₂ Fs f (wrap y)
fmap P [] f (wrap (param xs)) = param xs
fmap P ((F₁ , F₂) ∷ Fs) f (wrap (param xs)) = param (fmap F₂ Fs f (wrap xs) )
fmap I [] f (wrap (recur ⟨ x ⟩)) = recur (f (fmap _ [] f (wrap x)))
fmap I ((F₁ , F₂) ∷ Fs) f (wrap (recur xs)) = recur (fmap (F₁ ⊚ F₂) Fs f (wrap xs) )
fmap (G₁ ⊚ G₂) Fs f (wrap ⟨ xs ⟩) = ⟨ fmap G₁ ((G₁ , G₂) ∷ Fs) f (wrap xs) ⟩

cata : ∀ F → (f : ⟦ F ⟧ A R → R) → μ F A → R
cata F f ⟨ x ⟩ = f (fmap F [] f (wrap x))
