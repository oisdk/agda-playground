{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.List
open import Algebra using (Associative)
open import Data.List.Properties using (foldr-fusion)

infixr 5 _^_&_
record Spine (A : Type a) : Type a where
  inductive
  constructor _^_&_
  field
    depth : ℕ
    val : A
    tail : Maybe (Spine A)

module TheFold (f : A → A → A) (z : A) where
  infixr 5 _^_∹_
  _^_∹_ : ℕ → A → Spine A → Spine A
  n ^ x ∹ zero  ^ y & nothing = suc n ^ f x y & nothing
  n ^ x ∹ zero  ^ y & just xs = suc n ^ f x y ∹ xs
  n ^ x ∹ suc m ^ y & xs      = n ^ x & just (m ^ y & xs)

  ⟦_⟧⇑ : List A → Spine A
  ⟦_⟧⇑ = foldr (zero ^_∹_) (zero ^ z & nothing)

  ⟦_⟧⇓ : Spine A → A
  ⟦ _ ^ x & nothing ⟧⇓ = x
  ⟦ _ ^ x & just xs ⟧⇓ = f x ⟦ xs ⟧⇓

  treeFold : List A → A
  treeFold = ⟦_⟧⇓ ∘ ⟦_⟧⇑

  module _ (f-assoc : Associative f) where
    ∹-hom : ∀ n x xs → ⟦ n ^ x ∹ xs ⟧⇓ ≡ f x ⟦ xs ⟧⇓
    ∹-hom n x (zero  ^ _ & nothing) = refl
    ∹-hom n x (zero  ^ y & just xs) = ∹-hom (suc n) (f x y) xs ; f-assoc x y ⟦ xs ⟧⇓
    ∹-hom n x (suc _ ^ _ & nothing) = refl
    ∹-hom n x (suc _ ^ _ & just _ ) = refl

    treeFoldHom : ∀ xs → ⟦ ⟦ xs ⟧⇑ ⟧⇓ ≡ foldr f z xs
    treeFoldHom = foldr-fusion ⟦_⟧⇓ (zero ^ z & nothing) (∹-hom zero)
open TheFold using (treeFold; treeFoldHom) public
