{-# OPTIONS --allow-unsolved-metas #-}

module Choose where

open import Prelude
open import Data.List
open import Data.Vec

open import Data.Nat using (_+_)
open import Data.Nat.Properties using (_≤_; _<_)

private variable n m o k : ℕ

data Choose (A : Type) : ℕ → ℕ → Type where
  zl   : A → Choose A zero m
  zr   : Choose A (suc n) zero
  _**_ : Choose A (suc n) m
       → Choose A n m
       → Choose A (suc n) (suc m)

choose-shape : isProp (Choose ⊤ n m)
choose-shape (zl x) (zl y) = refl
choose-shape zr zr = refl
choose-shape (xl ** xr) (yl ** yr) = cong₂ _**_ (choose-shape xl yl) (choose-shape xr yr)

cmap : (A → B) → Choose A n m → Choose B n m
cmap f (zl x) = zl (f x)
cmap f zr = zr
cmap f (xs ** ys) = cmap f xs ** cmap f ys

choose : ∀ n → Vec A m → Choose (Vec A n) n m
choose zero    _        = zl []
choose (suc n) []       = zr
choose (suc n) (x ∷ xs) =
  choose (suc n) xs ** cmap (x ∷_) (choose n xs)

choose1 : Vec A m → Choose (Vec A 1) 1 m
choose1 []       = zr
choose1 (x ∷ xs) = choose1 xs ** zl (x ∷ [])

choose1-lemma : (xs : Vec A m) → choose 1 xs ≡ choose1 xs
choose1-lemma [] = refl
choose1-lemma (x ∷ xs) = cong (_** zl (x ∷ [])) (choose1-lemma xs)

zw : (A → B → C) → Choose A n m → Choose B n m → Choose C n m
zw f (zl x) (zl y) = zl (f x y)
zw f zr zr = zr
zw f (xl ** xr) (yl ** yr) = zw f xl yl ** zw f xr yr

sub : Vec A (suc n) → Vec (Vec A n) n
sub (x ∷ []) = []
sub (x ∷ xs@(_ ∷ _)) = xs ∷ vmap (x ∷_) (sub xs)

empty : A → Choose A n m
empty {n = zero}   x = zl x
empty {n = suc n} {m = zero} x = zr
empty {n = suc n} {m = suc m} x = empty x ** empty x

up : Choose A k m
   → 0 < k
   → k < m
   → Choose (Vec A k) (suc k) m
up (xs@(_ ** _) ** zl x)        p q = up xs tt {!!} ** {!!}
up (xs@(_ ** _) ** ys@(_ ** _)) p q = up xs tt {!!} ** zw _∷_ xs (up ys tt q)

-- up1-lemma : (xs : Vec A n) → up (choose 1 xs) ≡ cmap sub (choose 2 xs)
-- up1-lemma [] = refl
-- up1-lemma (x ∷ []) = refl
-- up1-lemma (x₁ ∷ x₂ ∷ xs) = cong₂ _**_ (up1-lemma (x₂ ∷ xs)) {!!}

-- up-prf : ∀ k (xs : Vec A m) → up (choose (suc k) xs) ≡ cmap sub (choose (suc (suc k)) xs)
-- up-prf _ [] = refl
-- up-prf zero    (x ∷ xs) = {!!}
-- up-prf (suc k) (x ∷ xs) = {!!}
