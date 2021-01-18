{-# OPTIONS --cubical --postfix-projections --guardedness #-}

module Data.RecursionSchemes where

open import Prelude

data Functor : Type (ℓsuc ℓzero) where
  _⊗_ : Functor → Functor → Functor
  _⊕_ : Functor → Functor → Functor
  Id : Functor
  Kn : Type₀ → Functor
  1# : Functor
  0# : Functor

record Identity (A : Type₀) : Type ℓzero where
  constructor identity
  field runIdentity : A
open Identity

record Constant (A : Type₀) : Type ℓzero where
  constructor constant
  field runConstant : A
open Constant


⟦_⟧ : Functor → Type₀ → Type₀
⟦ f ⊗ g ⟧ x = ⟦ f ⟧ x × ⟦ g ⟧ x
⟦ f ⊕ g ⟧ x = ⟦ f ⟧ x ⊎ ⟦ g ⟧ x
⟦ Id ⟧ x = Identity x
⟦ Kn x ⟧ _ = Constant x
⟦ 1# ⟧ x = ⊤
⟦ 0# ⟧ x = ⊥

variable
  F G : Functor

map : (A → B) → ⟦ F ⟧ A → ⟦ F ⟧ B
map {F = p₁ ⊗ p₂} f (xs , ys) = map {F = p₁} f xs , map {F = p₂} f ys
map {F = p₁ ⊕ p₂} f (inl x) = inl (map {F = p₁} f x)
map {F = p₁ ⊕ p₂} f (inr x) = inr (map {F = p₂} f x)
map {F = Id} f x = identity (f (runIdentity x ))
map {F = Kn x₁} f x = x
map {F = 1#} f x = tt

data μ (F : Functor) : Type _ where
  sup : ⟦ F ⟧ (μ F) → μ F

{-# TERMINATING #-}
mapFold : ∀ G F → (⟦ G ⟧ A → A) → ⟦ F ⟧ (μ G) → ⟦ F ⟧ A
mapFold G Id        alg (identity (sup x)) = identity (alg (mapFold G G alg x))
mapFold G (F₁ ⊗ F₂) alg (x , y) = mapFold G F₁ alg x , mapFold G F₂ alg y
mapFold G (F₁ ⊕ F₂) alg (inl x) = inl (mapFold G F₁ alg x)
mapFold G (F₁ ⊕ F₂) alg (inr x) = inr (mapFold G F₂ alg x)
mapFold G (Kn x)    alg xs = xs
mapFold G 1#        alg xs = xs

cata : (⟦ F ⟧ A → A) → μ F → A
cata alg (sup x) = alg (mapFold _ _ alg x)

LIST : Type₀ → Type₀
LIST A = μ (1# ⊕ (Kn A ⊗ Id))

foldr : {A B : Type₀} → (A → B → B) → B → LIST A → B
foldr f b = cata (either (const b) {!!})
