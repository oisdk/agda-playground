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

module Cons (f : A → A → A) where
  infixr 5 _^_∹_
  _^_∹_ : A → ℕ → Spine A → Spine A
  x ^ n ∹ &0 = x ^ n & &0
  x ^ n ∹ y ^ zero  & xs = f x y ^ suc n ∹ xs
  x ^ n ∹ y ^ suc m & xs = x ^ n & y ^ m & xs

  _∹_ : A → Spine A → Spine A
  _∹_ = _^ zero ∹_

module TreeFoldR (f : A → A → A) (z : A) where
  open Cons f public

  fold : Spine A → A
  fold &0 = z
  fold (x ^ n & xs) = f x (fold xs)

  spine : List A → Spine A
  spine = foldr _∹_ &0

  treeFold : List A → A
  treeFold = fold ∘ spine

  ∹-hom : Associative f → ∀ x xs → fold (x ^ n ∹ xs) ≡ f x (fold xs)
  ∹-hom p x &0 = refl
  ∹-hom p x (y ^ zero  & xs) = ∹-hom p (f x y) xs ; p x y (fold xs)
  ∹-hom p x (y ^ suc n & xs) = refl
  
  treeFoldHom : Associative f → ∀ xs → treeFold xs ≡ foldr f z xs
  treeFoldHom f-assoc = foldr-fusion fold &0 (∹-hom f-assoc)

module TreeFold1 (f : A → A → A) where
  open import Data.Maybe
  open import Data.Maybe.Properties
  open import Data.List.Properties

  f? : Maybe A → Maybe A → Maybe A
  f? nothing  = id
  f? (just x) = just ∘ maybe x (f x)

  open TreeFoldR f? nothing

  treeFoldMay : List A → Maybe A
  treeFoldMay = treeFold ∘ map just
  
  treeFoldMayHom : Associative f → ∀ xs → treeFoldMay xs ≡ foldrMay f xs
  treeFoldMayHom f-assoc xs = treeFoldHom f?-assoc (map just xs) ; map-fusion f? nothing just xs
    where
    f?-assoc : Associative f?
    f?-assoc nothing y z = refl
    f?-assoc (just x) nothing z = refl
    f?-assoc (just x) (just y) nothing = refl
    f?-assoc (just x) (just y) (just z) = cong just (f-assoc x y z)

  isJustSpine? : Spine (Maybe A) → Bool
  isJustSpine? &0 = false
  isJustSpine? (x ^ y & xs) = is-just x

  IsJustSpine : Spine (Maybe A) → Type
  IsJustSpine = T ∘ isJustSpine?

  isJust-cons : ∀ x n xs → IsJustSpine (just x ^ n ∹ xs)
  isJust-cons x n &0 = tt
  isJust-cons x n (y ^ zero  & xs) = isJust-cons (maybe x (f x) y) (suc n) xs
  isJust-cons x n (y ^ suc m & xs) = tt

  isJust-spine : ∀ xs → NonEmpty xs → IsJustSpine (spine (map just xs))
  isJust-spine (x ∷ xs) p = isJust-cons x 0 (spine (map just xs))

  isJust-fold : ∀ xs → IsJustSpine xs → IsJust (fold xs)
  isJust-fold (just _ ^ _ & _) _ = tt

  isJust-treeFoldMay : ∀ xs → NonEmpty xs → IsJust (treeFoldMay xs)
  isJust-treeFoldMay xs xsne = isJust-fold (spine (map just xs)) (isJust-spine xs xsne)

  treeFold1 : (xs : List A) → ⦃ NonEmpty xs ⦄ → A
  treeFold1 xs ⦃ xsne ⦄ = fromJust (treeFoldMay xs)
    where instance _ = isJust-treeFoldMay xs xsne

  -- treeFold1-hom : Associative f → ∀ xs → ⦃ xsne : NonEmpty xs ⦄ → treeFold1 xs ≡ foldr1 f xs
  -- treeFold1-hom f-assoc xs ⦃ xsne ⦄ = {!!}
open TreeFold1 using (treeFoldMay; treeFoldMayHom; treeFold1) public

open TreeFoldR using (treeFold; treeFoldHom) public

module TreeFoldL (f : A → A → A) (z : A) where
  open TreeFoldR (flip f) z using (_∹_; fold; ∹-hom) public

  spine : List A → Spine A
  spine = foldl (flip _∹_) &0

  treeFoldL : List A → A
  treeFoldL = fold ∘ spine

  treeFoldLHom : Associative f → ∀ xs → treeFoldL xs ≡ foldl f z xs
  treeFoldLHom p = foldl-fusion fold &0 (flip (∹-hom λ x y z → sym (p z y x)))

open TreeFoldL using (treeFoldL; treeFoldLHom) public

module StrictCons (f : A → A → A) where
  infixr 5 _^_∹_
  _^_∹_ : A → ℕ → Spine A → Spine A
  x ^ n ∹ &0 = x ^ n & &0
  x ^ n ∹ y ^ zero  & xs = (_^ suc n ∹ xs) $! (f x y)
  x ^ n ∹ y ^ suc m & xs = x ^ n & y ^ m & xs

  _∹_ : A → Spine A → Spine A
  _∹_ = _^ zero ∹_

  private module Lazy = Cons f

  strict-lazy-cons : ∀ x n xs → x ^ n ∹ xs ≡ x Lazy.^ n ∹ xs
  strict-lazy-cons x n &0 = refl
  strict-lazy-cons x n (y ^ zero  & xs) = $!-≡ (_^ suc n ∹ xs) (f x y) ; strict-lazy-cons (f x y) (suc n) xs
  strict-lazy-cons x n (y ^ suc m & xs) = refl

module TreeFoldL′ (f : A → A → A) (z : A) where
  open StrictCons (flip f)

  spine : List A → Spine A
  spine = foldl′ (flip _∹_) &0

  private module Lazy = TreeFoldL f z

  open Lazy using (fold)

  treeFoldL′ : List A → A
  treeFoldL′ = fold ∘ spine

  treeFoldL′Hom : Associative f → ∀ xs → treeFoldL′ xs ≡ foldl f z xs
  treeFoldL′Hom p xs =
    cong fold (foldl′-foldl (flip _∹_) &0 xs ; cong (λ c → foldl c &0 xs) (funExt λ ys → funExt λ y → strict-lazy-cons y 0 ys)) ;
    Lazy.treeFoldLHom p xs

open TreeFoldL′ using (treeFoldL′; treeFoldL′Hom) public
