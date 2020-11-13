{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.List
open import Algebra using (Associative)
open import Data.List.Properties using (foldr-fusion)

mutual
  infixr 5 _^_&_ ∹_
  data Tail {a} (A : Type a) : Type a where
    [] : Tail A
    ∹_ : Spine A → Tail A

  record Spine {a} (A : Type a) : Type a where
    inductive
    constructor _^_&_
    field
      depth : ℕ
      val : A
      tail : Tail A

module TheFold {a} {A : Type a} (f : A → A → A) (z : A) where
  infixr 5 _^_∹_
  _^_∹_ : ℕ → A → Spine A → Spine A
  n ^ x ∹ zero  ^ y & []   = suc n ^ f x y & []
  n ^ x ∹ zero  ^ y & ∹ xs = suc n ^ f x y ∹ xs
  n ^ x ∹ suc m ^ y & xs   = n ^ x & ∹ m ^ y & xs

  ⟦_⟧⇑ : List A → Spine A
  ⟦_⟧⇑ = foldr (zero ^_∹_) (zero ^ z & [])

  ⟦_⟧⇓ : Spine A → A
  ⟦ _ ^ x & []   ⟧⇓ = x
  ⟦ _ ^ x & ∹ xs ⟧⇓ = f x ⟦ xs ⟧⇓

  treeFold : List A → A
  treeFold = ⟦_⟧⇓ ∘ ⟦_⟧⇑

  module _ (f-assoc : Associative f) where
    ∹-hom : ∀ n x xs → ⟦ n ^ x ∹ xs ⟧⇓ ≡ f x ⟦ xs ⟧⇓
    ∹-hom n x (zero  ^ _ & [])   = refl
    ∹-hom n x (zero  ^ y & ∹ xs) = ∹-hom (suc n) (f x y) xs ; f-assoc x y ⟦ xs ⟧⇓
    ∹-hom n x (suc _ ^ _ & [])  = refl
    ∹-hom n x (suc _ ^ _ & ∹ _) = refl

    treeFoldHom : ∀ xs → ⟦ ⟦ xs ⟧⇑ ⟧⇓ ≡ foldr f z xs
    treeFoldHom = foldr-fusion ⟦_⟧⇓ (zero ^ z & []) (∹-hom zero)
open TheFold using (treeFold; treeFoldHom) public
