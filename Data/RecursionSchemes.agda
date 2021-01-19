{-# OPTIONS --cubical #-}

module Data.RecursionSchemes where

variable
  A : Set

record ⊤ : Set where constructor tt

data Functor : Set where
  U I : Functor

mutual
  ⟦_⟧ : Functor → Set → Set
  ⟦ U ⟧ A = ⊤
  ⟦ I ⟧ A = A

  data μ (F : Functor) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

record Wrap (A : Set) : Set where
  constructor [_]
  field unwrap : A

fmap : ∀ F G → (f : ⟦ F ⟧ A → A) → Wrap (⟦ G ⟧ (μ F)) → ⟦ G ⟧ A
cata : ∀ F → (f : ⟦ F ⟧ A → A) → μ F → A

fmap F U _ xs = tt
fmap F I f [ xs ] = cata F f xs

cata F f ⟨ x ⟩ = f (fmap F F f [ x ])
