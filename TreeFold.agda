{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.List
open import Algebra using (Associative)
open import Data.List.Properties using (foldr-fusion)

data Bit : Type₀ where
  1ᵇ 2ᵇ : Bit

mutual
  infixr 5 _&_&_ ∹_
  data Tail {a} (A : Type a) : Type a where
    [] : Tail A
    ∹_ : Spine A → Tail A

  record Spine {a} (A : Type a) : Type a where
    inductive
    constructor _&_&_
    field
      bit : Bit
      val : A
      tail : Tail A

module TheFold {a} {A : Type a} (f : A → A → A) (z : A) where
  mutual
    infixr 5 _∹_ _∹⋆_
    _∹_ : A → Spine A → Spine A
    x ∹ 1ᵇ & y & xs = 2ᵇ & f x y & xs
    x ∹ 2ᵇ & y & xs = 1ᵇ & x & y ∹⋆ xs

    _∹⋆_ : A → Tail A → Tail A
    x ∹⋆ []   = ∹ 1ᵇ & x & []
    x ∹⋆ ∹ xs = ∹ x ∹ xs

  ⟦_⟧⇑ : List A → Spine A
  ⟦_⟧⇑ = foldr _∹_ (1ᵇ & z & [])

  ⟦_⟧⇓ : Spine A → A
  ⟦ _ & x & []   ⟧⇓ = x
  ⟦ _ & x & ∹ xs ⟧⇓ = f x ⟦ xs ⟧⇓

  treeFold : List A → A
  treeFold = ⟦_⟧⇓ ∘ ⟦_⟧⇑

  module _ (f-assoc : Associative f) where
    ∹-hom : ∀ x xs → ⟦ x ∹ xs ⟧⇓ ≡ f x ⟦ xs ⟧⇓
    ∹-hom x (1ᵇ & y & []) = refl
    ∹-hom x (1ᵇ & y & ∹ xs) = f-assoc x y ⟦ xs ⟧⇓
    ∹-hom x (2ᵇ & y & []) = refl
    ∹-hom x (2ᵇ & y & ∹ xs) = cong (f x) (∹-hom y xs)

    treeFoldHom : ∀ xs → ⟦ ⟦ xs ⟧⇑ ⟧⇓ ≡ foldr f z xs
    treeFoldHom = foldr-fusion ⟦_⟧⇓ (1ᵇ & z & []) ∹-hom
open TheFold using (treeFold; treeFoldHom) public
