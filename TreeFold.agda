{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.List
open import Algebra using (Associative)
open import Data.List.Properties using (foldr-fusion; foldl-fusion; foldl′-foldl)

infixr 5 _^_&_
data Spine (A : Type a) : Type a where
  &0 : Spine A
  _^_&_ : A → ℕ → Spine A → Spine A

private variable n : ℕ

sing : A → Spine A
sing = _^ zero & &0

module TreeFoldR (f : A → A → A) (z : A) where
  infixr 5 _^_∹_
  _^_∹_ : A → ℕ → Spine A → Spine A
  x ^ n ∹ &0 = x ^ n & &0
  x ^ n ∹ y ^ zero  & xs = f x y ^ suc n & xs
  x ^ n ∹ y ^ suc m & xs = x ^ n & y ^ m & xs

  _∹_ : A → Spine A → Spine A
  _∹_ = _^ zero ∹_

  ⟦_⟧⇓ : Spine A → A
  ⟦ &0 ⟧⇓ = z
  ⟦ x ^ n & xs ⟧⇓ = f x ⟦ xs ⟧⇓

  ∹-hom : Associative f → ∀ x xs → ⟦ x ^ n ∹ xs ⟧⇓ ≡ f x ⟦ xs ⟧⇓
  ∹-hom p x &0 = refl
  ∹-hom p x (y ^ zero  & xs) = p x y ⟦ xs ⟧⇓
  ∹-hom p x (y ^ suc n & xs) = refl

  ⟦_⟧⇑ : List A → Spine A
  ⟦_⟧⇑ = foldr _∹_ &0

  treeFold : List A → A
  treeFold = ⟦_⟧⇓ ∘ ⟦_⟧⇑
  
  treeFoldHom : Associative f → ∀ xs → treeFold xs ≡ foldr f z xs
  treeFoldHom f-assoc = foldr-fusion ⟦_⟧⇓ &0 (∹-hom f-assoc)

open TreeFoldR using (treeFold; treeFoldHom) public

-- -- module TreeFoldL (f : A → A → A) (z : A) where
-- --   open BinaryOps (flip f) public

-- --   ⟦_⟧⇑ : List A → Spine A
-- --   ⟦_⟧⇑ = foldl (flip _∹_) (sing z)

-- --   treeFoldL : List A → A
-- --   treeFoldL = ⟦_⟧⇓ ∘ ⟦_⟧⇑

-- --   treeFoldLHom : Associative f → ∀ xs → treeFoldL xs ≡ foldl f z xs
-- --   treeFoldLHom f-assoc = foldl-fusion ⟦_⟧⇓ (sing z) (flip (∹-hom (λ x y z → sym (f-assoc z y x))))

-- -- open TreeFoldL using (treeFoldL; treeFoldLHom)

-- -- module TreeFoldL′ (f : A → A → A) (z : A) where
-- --   infixr 5 _^_∹_
-- --   _^_∹_ : ℕ → A → Spine A → Spine A
-- --   n ^ x ∹ zero  ^ y & &0 = let! xy =! f y x in! suc n ^ xy & &0
-- --   n ^ x ∹ zero  ^ y & just xs = let! xy =! f y x in! suc n ^ xy ∹ xs
-- --   n ^ x ∹ suc m ^ y & xs      = n ^ x & just (m ^ y & xs)

-- --   _∹_ : A → Spine A → Spine A
-- --   _∹_ = zero ^_∹_

-- --   ⟦_⟧⇓ : Spine A → A
-- --   ⟦ _ ^ x & &0 ⟧⇓ = x
-- --   ⟦ _ ^ x & just xs ⟧⇓ = let! fxs =! ⟦ xs ⟧⇓ in! f fxs x

-- --   ⟦_⟧⇑ : List A → Spine A
-- --   ⟦_⟧⇑ = foldl′ (flip (_∹_)) (sing z)

-- --   treeFoldL′ : List A → A
-- --   treeFoldL′ = ⟦_⟧⇓ ∘ ⟦_⟧⇑

-- --   module Lazy = TreeFoldL f z

-- --   strict-cons : ∀ n x xs → n ^ x ∹ xs ≡ n Lazy.^ x ∹ xs
-- --   strict-cons n x (zero  ^ y & &0) = $!-≡ (suc n ^_& &0) (f y x)
-- --   strict-cons n x (zero  ^ y & just xs) = $!-≡ (suc n ^_∹ xs) (f y x) ; strict-cons (suc n) (f y x) xs
-- --   strict-cons n x (suc m ^ y & xs)      = refl

-- --   strict-spine : ∀ xs → ⟦ xs ⟧⇑ ≡ Lazy.⟦ xs ⟧⇑
-- --   strict-spine xs = foldl′-foldl (flip (_∹_)) (sing z) xs ; cong (λ c → foldl c (sing z) xs) (funExt (λ y → funExt (λ x → strict-cons zero x y)))

-- --   strict-collapse : ∀ xs → ⟦ xs ⟧⇓ ≡ Lazy.⟦ xs ⟧⇓
-- --   strict-collapse (_ ^ x & &0) = refl
-- --   strict-collapse (_ ^ x & just xs) = $!-≡ (flip f x) ⟦ xs ⟧⇓ ; cong (flip f x) (strict-collapse xs)

-- --   strict-treeFoldL : ∀ xs → treeFoldL′ xs ≡ Lazy.treeFoldL xs
-- --   strict-treeFoldL xs = cong ⟦_⟧⇓ (strict-spine xs) ; strict-collapse Lazy.⟦ xs ⟧⇑

-- --   treeFoldL′Hom : Associative f → ∀ xs → treeFoldL′ xs ≡ foldl f z xs
-- --   treeFoldL′Hom f-assoc xs = strict-treeFoldL xs ; Lazy.treeFoldLHom f-assoc xs

-- -- open TreeFoldL′ using (treeFoldL′; strict-treeFoldL; treeFoldL′Hom)
