{-# OPTIONS --safe #-}

module Choose.Indexed where

open import Prelude
open import Data.Vec

private variable n m k : ℕ

data Choice : ℕ → ℕ → Type where
  done : Choice zero zero
  keep : Choice n m → Choice (suc n) (suc m)
  drop : Choice n m → Choice n (suc m)

Choose : Type → ℕ → ℕ → Type
Choose A n m = Choice n m → A

choose : Vec A m → Choose (Vec A n) n m
choose _        done     = []
choose (x ∷ xs) (drop i) = choose xs i
choose (x ∷ xs) (keep i) = x ∷ choose xs i

sub : Vec A (suc n) → Vec (Vec A n) n
sub {n = zero}  _        = []
sub {n = suc _} (x ∷ xs) = xs ∷ vmap (x ∷_) (sub xs)

up  : Choose A k m → Choose (Vec A k) (suc k) m
up {k = zero}  _  _        = []
up {k = suc k} xs (drop i) = up (xs ∘ drop) i
up {k = suc k} xs (keep i) = xs (drop i) ∷ up (xs ∘ keep) i

up-nat : ∀ (f : A → B) (xs : Choose A n m) i → up (f ∘ xs) i ≡ vmap f (up xs i)
up-nat {n = zero}  _ _  _        = refl
up-nat {n = suc _} f xs (drop i) = up-nat f (xs ∘ drop) i
up-nat {n = suc _} f xs (keep i) =
  cong (f (xs (drop i)) ∷_) (up-nat f (xs ∘ keep) i)

up-sub : ∀ n (xs : Vec A m) (i : Choice (suc n) m) 
       → up (choose xs) i ≡ sub (choose xs i)
up-sub zero    _        _        = refl
up-sub (suc n) (x ∷ xs) (drop i) = up-sub (suc n) xs i
up-sub (suc n) (x ∷ xs) (keep i) = 
  cong
    (choose xs i ∷_)
    (up-nat (x ∷_) (choose xs) i ; cong (vmap (x ∷_)) (up-sub n xs i))

open import Choose
  using (⟨_⟩; ⟨⟩; _**_)
  renaming (Choose to Choose′)

lookup : Choose′ A n m → Choose A n m
lookup ⟨ x ⟩ _ = x
lookup (xs ** ys) (drop i) = lookup xs i
lookup (xs ** ys) (keep i) = lookup ys i
