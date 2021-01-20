{-# OPTIONS --without-K #-}

module Data.RecursionSchemes where

open import Function
open import Data.Sum
open import Data.Sigma.Base
open import Level
open import Data.Unit
open import Data.List.Base using (List; _∷_; []; foldr)

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

-- alg : Functor → Type₀ → Type₀
-- alg G x = μ G x


-- comps : Functor → List Functor → Type₀ → Type₀
-- comps F xs A = foldr alg ( A) xs

-- go : ∀ G Fs → (A → B) → Wrap (⟦ G ⟧ (comps F Fs A) (comps F Fs (μ F A))) → ⟦ G ⟧ (comps F Fs B) (comps F Fs (μ F B))
-- go U         Fs f xs = tt
-- go (G₁ ⊕ G₂) Fs f (wrap (inl x)) = inl (go G₁ Fs f (wrap x))
-- go (G₁ ⊕ G₂) Fs f (wrap (inr x)) = inr (go G₂ Fs f (wrap x))

-- go (G₁ ⊗ G₂) Fs f (wrap (x , y)) = go G₁ Fs f (wrap x) , go G₂ Fs f (wrap y)

-- go P         Fs f        (wrap (param xs))            = {!!} -- param (f xs)
-- -- go P         (F₂ ∷ Fs) f (wrap (param ⟨ xs ⟩)) =  param  ⟨ go F₂ Fs f (wrap xs) ⟩

-- go I         Fs       f (wrap (recur xs)) = {!!} -- recur ⟨ go _ [] f (wrap xs) ⟩
-- -- go I         (F ∷ Fs) f (wrap (recur ⟨ xs ⟩)) = recur ⟨ go _ (F ∷ Fs) f (wrap xs) ⟩

-- go (G₁ ⊚ G₂) Fs f (wrap ⟨ xs ⟩) =  ⟨ go G₁ {!Fs!} {!f!} (wrap xs) ⟩

-- -- cata : (⟦ F ⟧ A R → R) → μ F A → R
-- -- cata alg ⟨ x ⟩ = alg (go _ _ id alg (wrap x))
-- --   where
-- --   go : ∀ F G → (A → B) → (⟦ F ⟧ A R → R) → Wrap (⟦ G ⟧ A (μ F A)) → ⟦ G ⟧ B R
-- --   go F U         g _ xs = tt
-- --   go F I         g f (wrap (recur xs)) = recur (cata f xs)
-- --   go F P         g f (wrap (param xs)) = param (g xs)
-- --   go F (G₁ ⊕ G₂) g f (wrap (inl x)) = inl (go F G₁ g f (wrap x))
-- --   go F (G₁ ⊕ G₂) g f (wrap (inr x)) = inr (go F G₂ g f (wrap x))
-- --   go F (G₁ ⊗ G₂) g f (wrap (x , y)) = go F G₁ g f (wrap x) , go F G₂ g f (wrap y)
-- --   go F (G₁ ⊚ G₂) g f (wrap xs) = {!!} -- mapμ (go F G₂ g f ∘′ wrap) xs
