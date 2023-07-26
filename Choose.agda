{-# OPTIONS --allow-unsolved-metas #-}

module Choose where

open import Prelude hiding (_⟨_⟩_)
open import Data.List
open import Data.Vec
open import Path.Reasoning

private variable n m k : ℕ

data Choose (A : Type) : ℕ → ℕ → Type where
  ⟨_⟩   : A → Choose A zero m
  ⟨⟩    : Choose A (suc n) zero
  _**_ : Choose A (suc n) m
       → Choose A n m
       → Choose A (suc n) (suc m)

cmap : (A → B) → Choose A n m → Choose B n m
cmap f ⟨ x ⟩      = ⟨ f x ⟩
cmap f ⟨⟩         = ⟨⟩
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

fill : ∀ n m → A → Choose A n m
fill zero    m       x = ⟨ x ⟩
fill (suc n) zero    x = ⟨⟩
fill (suc n) (suc m) x = fill (suc n) m x ** fill n m x

up  : Choose A k m → Choose (Vec A k) (suc k) m
up ⟨ _ ⟩       = fill _ _ []
up ⟨⟩          = ⟨⟩ 
up (xs ** ys) = up xs ** zw _∷_ xs (up ys)

private variable D E : Type

zw-cmap-cmap : (f : B → D → E) (g : A → B) (h : C → D) (xs : Choose A n m) (ys : Choose C n m)
             → zw f (cmap g xs) (cmap h ys) ≡ zw (λ x y → f (g x) (h y)) xs ys
zw-cmap-cmap f g h ⟨ x ⟩ ⟨ y ⟩ = refl
zw-cmap-cmap f g h ⟨⟩ ⟨⟩ = refl
zw-cmap-cmap f g h (xl ** xr) (yl ** yr) =
  cong₂ _**_ (zw-cmap-cmap f g h xl yl) (zw-cmap-cmap f g h xr yr)

cmap-zw : (f : C → D) (g : A → B → C) (xs : Choose A n m) (ys : Choose B n m)
        → cmap f (zw g xs ys) ≡ zw (λ x y → f (g x y)) xs ys
cmap-zw f g ⟨ x ⟩ ⟨ y ⟩ = refl
cmap-zw f g ⟨⟩ ⟨⟩ = refl
cmap-zw f g (xsₗ ** xsᵣ) (ysₗ ** ysᵣ) =
  cong₂ _**_ (cmap-zw f g xsₗ ysₗ) (cmap-zw f g xsᵣ ysᵣ)

choose-prop : isProp A → isProp (Choose A n m)
choose-prop prop ⟨ x ⟩ ⟨ y ⟩ = cong ⟨_⟩ (prop x y)
choose-prop prop ⟨⟩ ⟨⟩ = refl
choose-prop prop (xsₗ ** xsᵣ) (ysₗ ** ysᵣ) =
  cong₂ _**_ (choose-prop prop xsₗ ysₗ) (choose-prop prop xsᵣ ysᵣ)

up-nat : (f : A → B) (xs : Choose A n m) → up (cmap f xs) ≡ cmap (vmap f) (up xs)
up-nat f ⟨ x ⟩ = choose-prop isProp-[] _ _
up-nat f ⟨⟩ = refl
up-nat f (xs ** ys) =
  cong₂ _**_ (up-nat f xs) $

     zw _∷_ (cmap f xs) (up (cmap f ys))
                                                 ≡⟨ cong (zw _∷_ _) (up-nat f ys) ⟩
     zw _∷_ (cmap f xs) (cmap (vmap f) (up ys))
                                                 ≡⟨ zw-cmap-cmap _∷_ f (vmap f) xs (up ys) ⟩
     zw (λ z zs → vmap f (z ∷ zs)) xs (up ys)
                                                 ≡˘⟨ cmap-zw (vmap f) _∷_ xs (up ys) ⟩
     cmap (vmap f) (zw _∷_ xs (up ys)) ∎ 

cmap-comp : (g : B → C) (f : A → B) (xs : Choose A n m)
          → cmap g (cmap f xs) ≡ cmap (g ∘ f) xs
cmap-comp g f ⟨ x ⟩ = refl
cmap-comp g f ⟨⟩ = refl
cmap-comp g f (xsₗ ** xsᵣ) = cong₂ _**_ (cmap-comp g f xsₗ) (cmap-comp g f xsᵣ)

zw-sub : ∀ x (xs : Choose (Vec A (suc k)) n m)
       → cmap sub (cmap (x ∷_) xs) ≡ zw _∷_ xs (cmap (vmap (x ∷_) ∘ sub) xs)
zw-sub x ⟨ _ ∷ _ ⟩ = refl
zw-sub x ⟨⟩ = refl
zw-sub x (xs ** ys) = cong₂ _**_ (zw-sub x xs) (zw-sub x ys)

up-sub : ∀ n (xs : Vec A m) → up (choose n xs) ≡ cmap sub (choose (suc n) xs)
up-sub zero    xs = choose-prop isProp-[] _ _
up-sub (suc n) [] = refl
up-sub (suc n) (x ∷ xs) =
  cong₂ _**_ (up-sub (suc n) xs) $

    zw _∷_ (choose (suc n) xs) (up (cmap (x ∷_) (choose n xs)))
                                                                                     ≡⟨ cong (zw _∷_ _) (up-nat (x ∷_) (choose n xs)) ⟩
    zw _∷_ (choose (suc n) xs) (cmap (vmap (x ∷_)) (up (choose n xs)))
                                                                                     ≡⟨ cong (zw _∷_ _) (cong (cmap (vmap (x ∷_))) (up-sub n xs)) ⟩
    zw _∷_ (choose (suc n) xs) (cmap (vmap (x ∷_)) (cmap sub (choose (suc n) xs)))
                                                                                     ≡⟨ cong (zw _∷_ _) (cmap-comp _ _ _) ⟩
    zw _∷_ (choose (suc n) xs) (cmap (vmap (x ∷_) ∘ sub) (choose (suc n) xs))
                                                                                     ≡˘⟨ zw-sub x (choose (suc n) xs) ⟩
    cmap sub (cmap (x ∷_) (choose (suc n) xs)) ∎
