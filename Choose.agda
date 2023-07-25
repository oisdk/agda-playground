{-# OPTIONS --allow-unsolved-metas #-}

module Choose where

open import Prelude hiding (a; b; c)
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

choose′ : ∀ n → Vec A m → (Vec A n → B) → Choose B n m
choose′ zero    _        k = zl (k [])
choose′ (suc n) []       k = zr
choose′ (suc n) (x ∷ xs) k =
  choose′ (suc n) xs k ** choose′ n xs (k ∘ _∷_ x)


data Char : Type where a b c d : Char

e1 : Choose (Vec Char _) _ _
e1 = choose′ 2 (a ∷ b ∷ c ∷ d ∷ []) id

sub : Vec A (suc n) → Vec (Vec A n) n
sub (x ∷ []) = []
sub (x ∷ xs@(_ ∷ _)) = xs ∷ vmap (x ∷_) (sub xs)

e2 : Choose _ _ _
e2 = choose′ 3 (a ∷ b ∷ c ∷ d ∷ []) sub

choose1 : Vec A m → (Vec A 1 → B) → Choose B 1 m
choose1 []       k = zr
choose1 (x ∷ xs) k = choose1 xs k ** zl (k (x ∷ []))

choose1-lemma : (xs : Vec A m) → choose′ 1 xs id ≡ choose1 xs id
choose1-lemma [] = refl
choose1-lemma (x ∷ xs) = cong (_** zl (x ∷ [])) (choose1-lemma xs)

zw : (A → B → C) → Choose A n m → Choose B n m → Choose C n m
zw f (zl x) (zl y) = zl (f x y)
zw f zr zr = zr
zw f (xl ** xr) (yl ** yr) = zw f xl yl ** zw f xr yr

empty : A → Choose A n m
empty {n = zero} x = zl x
empty {n = suc n} {m = zero} x = zr
empty {n = suc n} {m = suc m} x = empty x ** empty x

up : Choose A (suc k) m
   → Choose (Vec A (suc k)) (suc (suc k)) m
up zr = zr
up (zr ** _) = zr ** zr
up (xs@(_ ** _) ** ys@(_ ** _)) = up xs ** zw _∷_ xs (up ys)
up (xs@(_ ** _) ** zl _) = up xs ** cmap (_∷ []) xs

lemma : ∀ x (xs : Vec A n) → cmap (_∷ []) (choose′ 1 xs id) ≡ choose′ 1 xs (sub ∘′ (x ∷_))
lemma x [] = refl
lemma x₁ (x₂ ∷ xs) = cong₂ _**_ (lemma x₁ xs) refl

up1-lemma : (xs : Vec A n) → up (choose′ 1 xs id) ≡ choose′ 2 xs sub
up1-lemma [] = refl
up1-lemma (x₁ ∷ []) = refl
up1-lemma (x₁ ∷ x₂ ∷ xs) =
  cong₂ _**_ (up1-lemma (x₂ ∷ xs)) (cong₂ _**_ (lemma x₁ xs) refl)

up-prf : ∀ k (xs : Vec A m) → k < m → up (choose′ (suc k) xs id) ≡ choose′ (suc (suc k)) xs sub
up-prf _       []       p = refl
up-prf zero    (x ∷ xs) p = up1-lemma (x ∷ xs)
up-prf (suc k) (x ∷ xs) p = {!!}
