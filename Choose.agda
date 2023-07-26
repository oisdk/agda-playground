{-# OPTIONS --allow-unsolved-metas #-}

module Choose where

open import Prelude hiding (a; b; c)
open import Data.List
open import Data.Vec

open import Data.Nat using (_+_)
open import Data.Nat.Properties using (_≤_; _<_)

private variable n m o k : ℕ

data Choose (A : Type) : ℕ → ℕ → Type where
  ⟨_⟩   : A → Choose A zero m
  ⟨⟩    : Choose A (suc n) zero
  _**_ : Choose A (suc n) m
       → Choose A n m
       → Choose A (suc n) (suc m)

cmap : (A → B) → Choose A n m → Choose B n m
cmap f ⟨ x ⟩ = ⟨ f x ⟩
cmap f ⟨⟩ = ⟨⟩
cmap f (xs ** ys) = cmap f xs ** cmap f ys

choose : ∀ n → Vec A m → Choose (Vec A n) n m
choose zero    _        = ⟨ [] ⟩
choose (suc n) []       = ⟨⟩ 
choose (suc n) (x ∷ xs) = choose (suc n) xs ** cmap (x ∷_) (choose n xs)

sub : Vec A (suc n) → Vec (Vec A n) n
sub (x ∷ []) = []
sub (x ∷ xs@(_ ∷ _)) = xs ∷ vmap (x ∷_) (sub xs)

zw : (A → B → C) → Choose A n m → Choose B n m → Choose C n m
zw f ⟨ x ⟩ ⟨ y ⟩ = ⟨ f x y ⟩
zw f ⟨⟩ ⟨⟩ = ⟨⟩
zw f (xsₗ ** xsᵣ) (ysₗ ** ysᵣ) = zw f xsₗ ysₗ ** zw f xsᵣ ysᵣ

sing : ∀ m → A → Choose A 1 m
sing zero    x = ⟨⟩
sing (suc m) x = sing m x ** ⟨ x ⟩

up  : Choose A k m → Choose (Vec A k) (suc k) m
up ⟨ _ ⟩ = sing _ []
up ⟨⟩ = ⟨⟩ 
up (xs ** ys) = up xs ** zw _∷_ xs (up ys)

private variable D E : Type

zw-cmap-cmap : (f : B → D → E) (g : A → B) (h : C → D) (xs : Choose A n m) (ys : Choose C n m)
             → zw f (cmap g xs) (cmap h ys) ≡ zw (λ x y → f (g x) (h y)) xs ys
zw-cmap-cmap f g h ⟨ x ⟩ ⟨ y ⟩ = refl
zw-cmap-cmap f g h ⟨⟩ ⟨⟩ = refl
zw-cmap-cmap f g h (xl ** xr) (yl ** yr) = cong₂ _**_ (zw-cmap-cmap f g h xl yl) (zw-cmap-cmap f g h xr yr)

cmap-zw : (f : C → D) (g : A → B → C) (xs : Choose A n m) (ys : Choose B n m)
        → cmap f (zw g xs ys) ≡ zw (λ x y → f (g x y)) xs ys
cmap-zw f g ⟨ x ⟩ ⟨ y ⟩ = refl
cmap-zw f g ⟨⟩ ⟨⟩ = refl
cmap-zw f g (xl ** xr) (yl ** yr) = cong₂ _**_ (cmap-zw f g xl yl) (cmap-zw f g xr yr)

sing-nat : ∀ m (f : A → B) (x : A) → sing m (f x) ≡ cmap f (sing m x)
sing-nat zero    f x = refl
sing-nat (suc m) f x = cong (_** ⟨ f x ⟩) (sing-nat m f x)

up-nat : (f : A → B) (xs : Choose A n m) → up (cmap f xs) ≡ cmap (vmap f) (up xs)
up-nat f ⟨ x ⟩ = sing-nat _ (vmap f) []
up-nat f ⟨⟩ = refl
up-nat f (xs ** ys) =
  cong₂ _**_ (up-nat f xs)
    (cong (zw _∷_ (cmap f xs)) (up-nat f ys) ; zw-cmap-cmap _∷_ f (vmap f) xs (up ys) ; sym (cmap-zw (vmap f) _∷_ xs (up ys)))

cmap-comp : (g : B → C) (f : A → B) (xs : Choose A n m) → cmap g (cmap f xs) ≡ cmap (g ∘ f) xs
cmap-comp g f ⟨ x ⟩ = refl
cmap-comp g f ⟨⟩ = refl
cmap-comp g f (xs ** xs₁) = cong₂ _**_ (cmap-comp g f xs) (cmap-comp g f xs₁)

lemma₁ : ∀ x (xs : Vec A n) → zw _∷_ (choose 1 xs) (sing _ []) ≡ cmap sub (cmap  (x ∷_) (choose 1 xs))
lemma₁ x [] = refl
lemma₁ x₁ (x₂ ∷ xs) = cong₂ _**_ (lemma₁ x₁ xs) refl

up1-lemma : (xs : Vec A n) → up (choose 1 xs) ≡ cmap sub (choose 2 xs)
up1-lemma [] = refl
up1-lemma (x₁ ∷ []) = refl
up1-lemma (x₁ ∷ x₂ ∷ xs) =
  cong₂ _**_ (up1-lemma (x₂ ∷ xs)) (cong₂ _**_ (lemma₁ x₁ xs) refl)

lemma₃ : ∀ x (xs : Choose (Vec A (suc k)) n m) → cmap sub (cmap (x ∷_) xs) ≡ zw _∷_ xs (cmap (vmap (x ∷_) ∘ sub) xs)
lemma₃ x ⟨ _ ∷ _ ⟩ = refl
lemma₃ x ⟨⟩ = refl
lemma₃ x (xs ** ys) = cong₂ _**_ (lemma₃ x xs) (lemma₃ x ys)

up-prf : ∀ n (xs : Vec A m) → up (choose (suc n) xs) ≡ cmap sub (choose (suc (suc n)) xs)
up-prf _       []       = refl
up-prf zero    (x ∷ xs) = up1-lemma (x ∷ xs)
up-prf (suc n) (x₁ ∷ xs) =
  cong₂ _**_ (up-prf (suc n) xs)
    (cong (zw _∷_ _) (up-nat (x₁ ∷_) (choose (suc n) xs) ; cong (cmap (vmap (x₁ ∷_))) (up-prf n xs) ; cmap-comp _ _ _) ; sym (lemma₃ x₁ (choose (suc (suc n)) xs)))
