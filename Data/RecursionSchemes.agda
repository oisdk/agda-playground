{-# OPTIONS --cubical --postfix-projections --guardedness --allow-unsolved-metas #-}

module Data.RecursionSchemes where

open import Prelude hiding (I)
open import Data.Fin
open import Data.Vec.Iterated
open import Lens

record Identity (A : Type₀) : Type ℓzero where
  inductive
  constructor identity
  field runIdentity : A
open Identity

private
  variable
    n : ℕ


data Functor : Type₀ where
  U I P : Functor
  _⊗_ _⊕_ _⊚_ : Functor → Functor → Functor

mutual
  ⟦_⟧ : Functor → Type₀ → Type₀ → Type₀
  ⟦ U ⟧ A R = ⊤
  ⟦ I ⟧ A R = R
  ⟦ P ⟧ A R = A
  ⟦ F ⊕ G ⟧ A R = ⟦ F ⟧ A R ⊎ ⟦ G ⟧ A R
  ⟦ F ⊗ G ⟧ A R = ⟦ F ⟧ A R × ⟦ G ⟧ A R
  ⟦ F ⊚ G ⟧ A R = μ F (⟦ G ⟧ A R)

  data μ (F : Functor) (A : Type₀) : Type _ where
    ⟨_⟩ : ⟦ F ⟧ A (μ F A) → μ F A

variable
  R S : Type₀
  F G : Functor


-- map : (A → B) → (R → S) → ⟦ F ⟧ A R → ⟦ F ⟧ B S
-- map {F = U}     f g x = tt
-- map {F = I}     f g x = g x
-- map {F = P}     f g x = f x
-- map {F = F ⊕ G} f g (inl x) = inl (map f g x)
-- map {F = F ⊕ G} f g (inr x) = inr (map f g x)
-- map {F = F ⊗ G} f g (x , y) = map f g x , map f g y
-- map {F = F ⊚ G} f g ⟨ x ⟩ = ⟨ map {F = F} (map {F = G} f g) (map {F = F ⊚ G} f g) x ⟩

{-# TERMINATING #-}
mapFold : ∀ G F → (⟦ G ⟧ A R → R) → ⟦ F ⟧ B (μ G A) → ⟦ F ⟧ B R
mapFold G U         alg xs = tt
mapFold G I         alg ⟨ xs ⟩ = alg (mapFold G G alg xs)
mapFold G P         alg xs = xs
mapFold G (F₁ ⊗ F₂) alg (xs , ys) = mapFold G F₁ alg xs , mapFold G F₂ alg ys
mapFold G (F₁ ⊕ F₂) alg (inl x) = inl (mapFold G F₁ alg x)
mapFold G (F₁ ⊕ F₂) alg (inr x) = inr (mapFold G F₂ alg x)
mapFold G (F₁ ⊚ F₂) alg ⟨ xs ⟩ = {!!} -- ⟨ mapFold F₂ {!G ⊚ F₁ !} (mapFold {!!} {!!} alg) xs ⟩

-- mapFold : ∀ G F → (⟦ G ⟧ A → A) → ⟦ F ⟧ (μ G) → ⟦ F ⟧ A
-- mapFold G F alg xs = {!!}
-- mapFold G (F₁ ⊕ F₂) alg (x , y) = mapFold G F₁ alg x , mapFold G F₂ alg y
-- mapFold G (F₁ ⊗ F₂) alg (inl x) = inl (mapFold G F₁ alg x)
-- mapFold G (F₁ ⊗ F₂) alg (inr x) = inr (mapFold G F₂ alg x)
-- mapFold G (Val i)   alg xs = xs
-- mapFold G 1#        alg xs = xs

-- -- cata : (⟦ F ⟧ A → A) → μ F → A
-- -- cata alg (sup x) = alg (mapFold _ _ alg x)

-- -- LIST : Type₀ → Type₀
-- -- LIST A = μ (1# ⊗ (Kn A ⊕ Id))

-- -- foldr : {A B : Type₀} → (A → B → B) → B → LIST A → B
-- -- foldr f b = cata (either (const b) {!!})
