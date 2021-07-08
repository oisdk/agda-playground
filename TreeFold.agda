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

private variable n : ℕ

sing : A → Spine A
sing = zero ^_& nothing

module BinaryOps (_*_ : A → A → A) where
  infixr 5 _^_∹_
  _^_∹_ : ℕ → A → Spine A → Spine A
  n ^ x ∹ zero  ^ y & nothing = suc n ^ (x * y) & nothing
  n ^ x ∹ zero  ^ y & just xs = suc n ^ (x * y) ∹ xs
  n ^ x ∹ suc m ^ y & xs      = n ^ x & just (m ^ y & xs)

  _∹_ : A → Spine A → Spine A
  _∹_ = zero ^_∹_

  ⟦_⟧⇓ : Spine A → A
  ⟦ _ ^ x & nothing ⟧⇓ = x
  ⟦ _ ^ x & just xs ⟧⇓ = x * ⟦ xs ⟧⇓

  ∹-hom : Associative _*_ → ∀ x xs → ⟦ n ^ x ∹ xs ⟧⇓ ≡ x * ⟦ xs ⟧⇓
  ∹-hom _ x (zero  ^ _ & nothing) = refl
  ∹-hom p x (zero  ^ y & just xs) = ∹-hom p (x * y) xs ; p x y ⟦ xs ⟧⇓
  ∹-hom _ x (suc _ ^ _ & nothing) = refl
  ∹-hom _ x (suc _ ^ _ & just _ ) = refl

module TreeFoldR (f : A → A → A) (z : A) where
  open BinaryOps f

  ⟦_⟧⇑ : List A → Spine A
  ⟦_⟧⇑ = foldr _∹_ (sing z)

  treeFold : List A → A
  treeFold = ⟦_⟧⇓ ∘ ⟦_⟧⇑

  treeFoldHom : Associative f → ∀ xs → treeFold xs ≡ foldr f z xs
  treeFoldHom f-assoc = foldr-fusion ⟦_⟧⇓ (sing z) (∹-hom f-assoc)

open TreeFoldR using (treeFold; treeFoldHom) public

module TreeFoldL (f : A → A → A) (z : A) where
  open BinaryOps (flip f)

  ⟦_⟧⇑ : List A → Spine A
  ⟦_⟧⇑ = foldl (flip _∹_) (sing z)

  treeFoldL : List A → A
  treeFoldL = ⟦_⟧⇓ ∘ ⟦_⟧⇑

  treeFoldLHom : Associative f → ∀ xs → treeFoldL xs ≡ foldl f z xs
  treeFoldLHom f-assoc = foldl-fusion ⟦_⟧⇓ (sing z) (flip (∹-hom (λ x y z → sym (f-assoc z y x))))

open TreeFoldL using (treeFoldL; treeFoldLHom)
