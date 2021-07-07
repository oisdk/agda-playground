{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.List
open import Algebra using (Associative)
open import Data.List.Properties using (foldr-fusion; foldl-fusion)

infixr 5 _^_&_
record Spine (A : Type a) : Type a where
  inductive
  constructor _^_&_
  field
    zeroes : ℕ
    one : A
    tail : Maybe (Spine A)

module TheFold (f : A → A → A) where
  infixr 5 _^_∹_
  _^_∹_ : ℕ → A → Spine A → Spine A
  n ^ x ∹ zero  ^ y & nothing = suc n ^ f x y & nothing
  n ^ x ∹ zero  ^ y & just xs = suc n ^ f x y ∹ xs
  n ^ x ∹ suc m ^ y & xs      = n ^ x & just (m ^ y & xs)

  ⟦_⟧⇓ : Spine A → A
  ⟦ _ ^ x & nothing ⟧⇓ = x
  ⟦ _ ^ x & just xs ⟧⇓ = f x ⟦ xs ⟧⇓

  module _ (z : A) where

    ⟦_⟧⇑ : List A → Spine A
    ⟦_⟧⇑ = foldr (zero ^_∹_) (zero ^ z & nothing)

    treeFold : List A → A
    treeFold = ⟦_⟧⇓ ∘ ⟦_⟧⇑

    module _ (f-assoc : Associative f) where
      ∹-hom : ∀ {n} x xs → ⟦ n ^ x ∹ xs ⟧⇓ ≡ f x ⟦ xs ⟧⇓
      ∹-hom x (zero  ^ _ & nothing) = refl
      ∹-hom x (zero  ^ y & just xs) = ∹-hom (f x y) xs ; f-assoc x y ⟦ xs ⟧⇓
      ∹-hom x (suc _ ^ _ & nothing) = refl
      ∹-hom x (suc _ ^ _ & just _ ) = refl

      treeFoldHom : ∀ xs → ⟦ ⟦ xs ⟧⇑ ⟧⇓ ≡ foldr f z xs
      treeFoldHom = foldr-fusion ⟦_⟧⇓ (zero ^ z & nothing) ∹-hom
open TheFold using (treeFold; treeFoldHom) public

module TheLeftFold (f : A → A → A) where
  open TheFold (flip f) using (_^_∹_; ⟦_⟧⇓)

  module _ (z : A) where
    ⟦_⟧⇑ : List A → Spine A
    ⟦_⟧⇑ = foldl (flip (zero ^_∹_)) (zero ^ z & nothing)

    treeFoldL : List A → A
    treeFoldL = ⟦_⟧⇓ ∘ ⟦_⟧⇑

    module _ (f-assoc : Associative f) where
      ∹-hom : ∀ {n} x xs → ⟦ n ^ x ∹ xs ⟧⇓ ≡ f ⟦ xs ⟧⇓ x
      ∹-hom x (zero  ^ y & nothing) = refl
      ∹-hom x (zero  ^ y & just xs) = ∹-hom (f y x) xs ; sym (f-assoc ⟦ xs ⟧⇓ y x)
      ∹-hom x (suc m ^ y & nothing) = refl
      ∹-hom x (suc m ^ y & just xs) = refl

      treeFoldLHom : ∀ xs → ⟦ ⟦ xs ⟧⇑ ⟧⇓ ≡ foldl f z xs
      treeFoldLHom = foldl-fusion ⟦_⟧⇓ (zero ^ z & nothing) (flip ∹-hom)
open TheLeftFold using (treeFoldL; treeFoldLHom)
