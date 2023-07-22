{-# OPTIONS --allow-unsolved-metas #-}

module Choose where

open import Prelude
open import Data.List
open import Data.Vec

open import Data.Nat using (_+_)
open import Data.Nat.Properties using (_≤_)

private variable n m o : ℕ

data Choose (A : Type) : ℕ → ℕ → Type where
  zl   : A → Choose A zero (suc m)
  zr   : Choose A n zero
  _**_ : Choose A (suc n) m
       → Choose A n m
       → Choose A (suc n) (suc m)

cmap : (A → B) → Choose A n m → Choose B n m
cmap f (zl x) = zl (f x)
cmap f zr = zr
cmap f (xs ** ys) = cmap f xs ** cmap f ys

choose : ∀ n → Vec A m → Choose (List A) n m
choose n       []       = zr
choose zero    (_ ∷ _ ) = zl []
choose (suc n) (x ∷ xs) =
  choose (suc n) xs ** cmap (x ∷_) (choose n xs)

zw : (A → B → C) → Choose A n m → Choose B n m → Choose C n m
zw f (zl x) (zl y) = zl (f x y)
zw f zr zr = zr
zw f (xl ** xr) (yl ** yr) = zw f xl yl ** zw f xr yr

sub : List A → List (List A)
sub [] = []
sub (x ∷ xs) = xs ∷ map (x ∷_) (sub xs)

up : Choose A n m → Choose (List A) (suc n) m
up (zl x) = {!!}
up zr = zr
up (xs ** ys) = up xs ** zw _∷_ xs (up ys)

up-prf : ∀ n (xs : Vec A m) → up (choose n xs) ≡ cmap sub (choose (suc n) xs)
up-prf _ [] = refl
up-prf zero (x ∷ xs) = {!!}
up-prf (suc n) (x ∷ xs) = cong₂ _**_ (up-prf (suc n) xs) {!!}
