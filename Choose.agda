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

choose : ∀ n → Vec A m → Choose (Vec A n) n m
choose zero    _        = zl []
choose (suc n) []       = zr
choose (suc n) (x ∷ xs) =
  choose (suc n) xs ** cmap (x ∷_) (choose n xs)


data Char : Type where a b c d : Char

e1 : Choose (Vec Char _) _ _
e1 = choose 2 (a ∷ b ∷ c ∷ d ∷ [])

sub : Vec A (suc n) → Vec (Vec A n) n
sub (x ∷ []) = []
sub (x ∷ xs@(_ ∷ _)) = xs ∷ vmap (x ∷_) (sub xs)

e2 : Choose _ _ _
e2 = cmap sub (choose 3 (a ∷ b ∷ c ∷ d ∷ []) )

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

empty : A → Choose A n m
empty {n = zero} x = zl x
empty {n = suc n} {m = zero} x = zr
empty {n = suc n} {m = suc m} x = empty x ** empty x

up  : Choose A (suc k) m → Choose (Vec A (suc k)) (suc (suc k)) m
up′ : Choose A k m → Choose (Vec A k) (suc k) m

up′ (zl x) = empty []
up′ zr = zr
up′ ys@(_ ** _) = up ys

up zr = zr
up (xs ** ys) = up xs ** zw _∷_ xs (up′ ys)

up-nat : (f : A → B) (xs : Choose A (suc n) m) → up (cmap f xs) ≡ cmap (vmap f) (up xs)
up-nat f zr = refl
up-nat f (xs ** zl x) = cong₂ _**_ (up-nat f xs) {!!}
up-nat f (xs ** zr) = cong₂ _**_ (up-nat f xs) {!!}
up-nat f (xs ** (ys ** ys₁)) = cong₂ _**_ (up-nat f xs) {!!}

up′-nat : (f : A → B) (xs : Choose A n m) → up′ (cmap f xs) ≡ cmap (vmap f) (up′ xs)
up′-nat = {!!}

cmap-comp : (g : B → C) (f : A → B) (xs : Choose A n m) → cmap g (cmap f xs) ≡ cmap (g ∘ f) xs
cmap-comp = {!!}

lemma₁ : ∀ x (xs : Vec A n) → zw _∷_ (choose 1 xs) (empty []) ≡ cmap sub (cmap  (x ∷_) (choose 1 xs))
lemma₁ x [] = refl
lemma₁ x₁ (x₂ ∷ xs) = cong₂ _**_ (lemma₁ x₁ xs) refl

up1-lemma : (xs : Vec A n) → up (choose 1 xs) ≡ cmap sub (choose 2 xs)
up1-lemma [] = refl
up1-lemma (x₁ ∷ []) = refl
up1-lemma (x₁ ∷ x₂ ∷ xs) =
  cong₂ _**_ (up1-lemma (x₂ ∷ xs)) (cong₂ _**_ (lemma₁ x₁ xs) refl)


up-prf : ∀ n (xs : Vec A m) → up (choose (suc n) xs) ≡ cmap sub (choose (suc (suc n)) xs)

lemma₃ : ∀ x (xs : Choose (Vec A (suc k)) n m) → cmap sub (cmap (x ∷_) xs) ≡ zw _∷_ xs (cmap (vmap (x ∷_) ∘ sub) xs)
lemma₃ x (zl xs@(_ ∷ _)) = refl
lemma₃ x zr = refl
lemma₃ x (xs ** ys) = cong₂ _**_ (lemma₃ x xs) (lemma₃ x ys)

lemma₂ : ∀ (x : A) n (xs : Vec A m)
       → up′ {A = Vec A (suc (suc n))}  (cmap (x ∷_) (choose (suc n) xs)) ≡ cmap (λ z → vmap (x ∷_) (sub z)) (choose (suc (suc n)) xs)
lemma₂ x n xs = {!!}

up-prf _       []       = refl
up-prf zero    (x ∷ xs) = up1-lemma (x ∷ xs)
up-prf (suc n) (x₁ ∷ []) = refl
up-prf (suc n) (x₁ ∷ xs) =
  cong₂ _**_ (up-prf (suc n) xs) (cong (zw _∷_ _) (lemma₂ x₁ n _) ; sym (lemma₃ x₁ (choose (suc (suc n)) xs)))

e3 : Type
e3 = type-of (up-prf 3 (a ∷ b ∷ c ∷ d ∷ []) )
