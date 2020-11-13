{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.List
open import Algebra using (Associative)
open import Data.List.Properties using (foldr-fusion)

record Node {a} (A : Type a) : Type a where
  constructor node
  field
    bit : Bool
    val : A
open Node

Spine : Type a → Type a
Spine A = List (Node A)

module TheFold {a} {A : Type a} (f : A → A → A) (z : A) where
  infixr 5 _∹_
  _∹_ : A → Spine A → Spine A
  x ∹ [] = node false x ∷ []
  x ∹ (node false y ∷ xs) = node true (f x y) ∷ xs
  x ∹ (node true  y ∷ xs) = node false x ∷ y ∹ xs

  ⟦_⟧⇑ : List A → Spine A
  ⟦_⟧⇑ = foldr _∹_ []

  ⟦_⟧⇓ : Spine A → A
  ⟦_⟧⇓ = foldr (f ∘ val) z

  treeFold : List A → A
  treeFold = ⟦_⟧⇓ ∘ ⟦_⟧⇑

  module _ (f-assoc : Associative f) where
    ∹-hom : ∀ x xs → ⟦ _∹_ x xs ⟧⇓ ≡ f x ⟦ xs ⟧⇓
    ∹-hom x [] = refl
    ∹-hom x (node false y ∷ xs) = f-assoc x y ⟦ xs ⟧⇓
    ∹-hom x (node true  y ∷ xs) = cong (f x) (∹-hom y xs)

    treeFoldHom : ∀ xs → ⟦ ⟦ xs ⟧⇑ ⟧⇓ ≡ foldr f z xs
    treeFoldHom = foldr-fusion ⟦_⟧⇓ [] ∹-hom
open TheFold using (treeFold; treeFoldHom)
