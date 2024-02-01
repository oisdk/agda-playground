{-# OPTIONS --safe #-}

module Data.Permutation.Normalised.Norm where

open import Prelude hiding (_↔_)
open import Data.List hiding ([]; _∷_)
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Permutation.Swap _≟_
open import Data.Permutation.NonNorm _≟_
open import Data.Nat using (_+_)
open import Data.Permutation.Normalised.Definition
open import Data.List.Properties
open import Data.Maybe using (mapMaybe)
open import Data.Nat.Compare

swap-diff : ℕ → ℕ → Maybe (ℕ × ℕ)
swap-diff x y = mapMaybe (map₁ (bool′ x y)) (compare x y)

infixl 5 _⊙⟨_⟩
_⊙⟨_⟩ : Diffs → ℕ × ℕ → Diffs
⟨⟩ ⊙⟨ p ⟩ = ⟨⟩ ∘⟨ p ⟩
xs ∘⟨ yₛ , yₜ ⟩ ⊙⟨ xₛ , xₜ ⟩ = case compare xₛ yₛ of
  λ { equal           → maybe (xs ⊙+ suc xₛ) (λ lg → xs ⊙⟨ lg ⟩ ∘⟨ xₛ , yₜ ⟩) (swap-diff xₜ yₜ)
    ; (less    yₛ-xₛ-1) → xs ∘⟨ yₛ-xₛ-1 , yₜ ⟩ ∘⟨ xₛ , xₜ ⟩
    ; (greater xₛ-yₛ-1) → xs ⊙⟨ xₛ-yₛ-1 , xₜ ⟩ ∘⟨ yₛ , xₛ-yₛ-1 ↔ xₜ ⊙ yₜ ⟩
    }

[_]↓ : Swaps → Diffs
[_]↓ = foldr (flip _⊙⟨_⟩) ⟨⟩ ∘ catMaybes (uncurry swap-diff)

open import Path.Reasoning

⊙-cong : ∀ w x y z → does (w ↔ x ⊙ y ≟ z) ≡ does (y ≟ w ↔ x ⊙ z)
⊙-cong w x y z =
  both-do
    (w ↔ x ⊙ y ≟ z)
    (y ≟ w ↔ x ⊙ z)
    ((sym (⊙-alg-dup w x y) ;_ ∘′ cong (w ↔ x ⊙_)) iff (_; ⊙-alg-dup w x z ∘′ cong (w ↔ x ⊙_) ))

cons-swap : ∀ x y xs z → xs ⊙⟨ x , y ⟩ ⊙ z ≡ xs ⊙ x ↔ y ⊙ z
cons-swap₁ : ∀ x k y z xs n → xs ⊙⟨ k , y ⟩ ∘⟨ x , k ↔ y ⊙ z ⟩ ⊙ n ≡ xs ∘⟨ x , z         ⟩ ⊙ suc x + k ↔ y         ⊙ n
cons-swap₂ : ∀ x y xs z n   → xs ⊙⟨ y , z ⟩ ∘⟨ x , y         ⟩ ⊙ n ≡ xs ∘⟨ x , y         ⟩ ⊙ x         ↔ suc y + z ⊙ n
cons-swap₃ : ∀ x y z xs n   → xs ⊙⟨ y , z ⟩ ∘⟨ x , suc y + z ⟩ ⊙ n ≡ xs ∘⟨ x , suc y + z ⟩ ⊙ x         ↔ y         ⊙ n

cons-swap₁ (suc x) k y z xs (suc n) = cong suc (cons-swap₁ x k y z xs n)
cons-swap₁ (suc x) k y z xs zero = refl
cons-swap₁ zero k y z xs zero = cong suc (cons-swap k y xs (k ↔ y ⊙ z) ; cong (xs ⊙_) (⊙-alg-dup k y z))
cons-swap₁ zero k y z xs (suc n) = 
  xs ⊙⟨ k , y ⟩ ∘⟨ zero , k ↔ y ⊙ z ⟩ ⊙ suc n ≡⟨⟩
  (if does (k ↔ y ⊙ z ≟ n) then zero else suc (xs ⊙⟨ k , y ⟩ ⊙ n)) ≡⟨ cong (λ e → if does (k ↔ y ⊙ z ≟ n) then zero else suc e) (cons-swap k y xs n) ⟩
  (if does (k ↔ y ⊙ z ≟ n) then zero else suc (xs ⊙ k ↔ y ⊙ n)) ≡⟨ cong (bool′ (suc (xs ⊙ k ↔ y ⊙ n)) zero) (⊙-cong k y z n) ⟩
  (if does (z ≟ k ↔ y ⊙ n) then zero else suc (xs ⊙ k ↔ y ⊙ n)) ≡⟨⟩
  xs ∘⟨ zero , z ⟩ ⊙ suc (k ↔ y ⊙ n) ≡⟨⟩
  xs ∘⟨ zero , z ⟩ ⊙ suc k ↔ y ⊙ suc n ∎

cons-swap₂ (suc x) y xs z zero = refl
cons-swap₂ (suc x) y xs z (suc n) = cong suc (cons-swap₂ x y xs z n)
cons-swap₂ zero y xs z zero with does (y ≟ suc y + z) | why (y ≟ suc y + z)
... | false | p = cong suc $
  xs ⊙⟨ y , z ⟩ ⊙ y ≡⟨ cons-swap y z xs y ⟩
  xs ⊙ (y ↔ z ⊙ y) ≡⟨ cong (xs ⊙_) (⊙-· y z y ; swap-lhs y (suc y + z) ) ⟩
  xs ⊙ suc y + z ∎
... | true  | p = ⊥-elim (x≢sx+y y z p)
cons-swap₂ zero y xs z (suc n) with does (y ≟ n) | why (y ≟ n) | does (suc y + z ≟ n) | why (suc y + z ≟ n)
... | true  | y≡n | true  | sy+z≡n = ⊥-elim (x≢sx+y n z (sym sy+z≡n ; cong suc (cong (_+ z) y≡n)))
... | false | y≢n | true  | sy+z≡n = cong suc (cons-swap y z xs n ; cong (xs ⊙_) (⊙-· y z n ; cong (y ↔_· n) sy+z≡n ; swap-rhs y n))
... | false | y≢n | false | sy+z≢n = cong suc (cons-swap y z xs n ; cong (xs ⊙_) (⊙-· y z n ; swap-neq y _ n y≢n sy+z≢n) ) ; sym (cong (bool′ _ _) (it-doesn't (y ≟ n) y≢n))
... | true  | y≡n | false | sy+z≢n = sym (cong (bool′ _ _) (it-does (y ≟ n) y≡n))

cons-swap₃ (suc x) y z xs zero = refl
cons-swap₃ (suc x) y z xs (suc n) = cong suc (cons-swap₃ x y z xs n)
cons-swap₃ zero y z xs zero =
  suc (xs ⊙⟨ y , z ⟩ ⊙ suc y + z) ≡⟨ cong suc (cons-swap y z xs _) ⟩
  suc (xs ⊙ y ↔ z ⊙ suc y + z) ≡⟨ cong suc (cong (xs ⊙_) (⊙-· y z _ ; swap-rhs y _)) ⟩
  suc (xs ⊙ y) ≡˘⟨ cong (bool _ zero) (it-doesn't  (suc y + z ≟ y) (x≢sx+y y z ∘ sym)) ⟩
  xs ∘⟨ zero , suc y + z ⟩ ⊙ zero ↔ y ⊙ zero ∎
cons-swap₃ zero y z xs (suc n) with does (y ≟ n) | why (y ≟ n)
... | true | y≡n =
  (xs ⊙⟨ y , z ⟩ ∘⟨ zero , suc y + z ⟩ ⊙ suc n) ≡⟨ cong (bool′ _ _) (it-doesn't (suc y + z ≟ n) (x≢sx+y y z ∘ sym ∘ _; sym y≡n)) ⟩
  suc (xs ⊙⟨ y , z ⟩ ⊙ n) ≡⟨ cong suc (cons-swap y z xs n) ⟩
  suc (xs ⊙ y ↔ z ⊙ n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (⊙-· y z n) ⟩
  suc (xs ⊙ y ↔ suc y + z · n) ≡⟨ cong (λ e → suc (xs ⊙ e ↔ suc y + z · n)) y≡n ⟩
  suc (xs ⊙ n ↔ suc y + z · n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (swap-lhs n _)  ⟩
  suc (xs ⊙ suc y + z) ∎
... | false | y≢n with does (suc y + z ≟ n) | why (suc y + z ≟ n)
... | true | _ = refl
... | false | sy+z≢n =
  suc (xs ⊙⟨ y , z ⟩ ⊙ n) ≡⟨ cong suc (cons-swap y z xs n) ⟩
  suc (xs ⊙ y ↔ z ⊙ n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (⊙-· y z n) ⟩
  suc (xs ⊙ y ↔ suc y + z · n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (swap-neq y _ n y≢n sy+z≢n) ⟩
  suc (xs ⊙ n) ∎

cons-swap x y ⟨⟩ z = refl
cons-swap x y (xs ∘⟨ zₛ , zₜ ⟩) n with compare x zₛ | comparing x zₛ
... | less k | p =
  xs ∘⟨ k , zₜ ⟩ ∘⟨ x , y ⟩ ⊙ n ≡⟨ ⊙-alg-com x y (xs ∘⟨ k , zₜ ⟩) n ⟩
  xs ∘⟨ suc x + k , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ e , zₜ ⟩ ⊙ _) p ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ∎
... | greater k | p =
  xs ⊙⟨ k , y ⟩ ∘⟨ zₛ , k ↔ y ⊙ zₜ ⟩ ⊙ n ≡⟨ cons-swap₁ zₛ k y zₜ xs n ⟩
  (xs ∘⟨ zₛ , zₜ ⟩ ⊙ suc zₛ + k ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ zₛ , zₜ ⟩ ⊙ e ↔ y ⊙ n) p ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ x ↔ y ⊙ n ∎
... | equal | x≡zₛ with compare y zₜ | comparing y zₜ
... | equal | y≡zₜ =
  xs ⊙+ suc x ⊙ n ≡˘⟨ cong (xs ⊙+ suc x ⊙_) (cong (x ↔_⊙ x ↔ y ⊙ n) (sym y≡zₜ) ; ⊙-alg-dup x y n) ⟩
  (xs ⊙+ suc x ⊙ x ↔ zₜ ⊙ x ↔ y ⊙ n) ≡˘⟨ ⊙-alg-com x zₜ xs (x ↔ y ⊙ n) ⟩
  (xs ∘⟨ x , zₜ ⟩ ⊙ x ↔ y ⊙ n) ≡⟨ cong (λ e → (xs ∘⟨ e , zₜ ⟩ ⊙ x ↔ y ⊙ n)) x≡zₛ  ⟩
  (xs ∘⟨ zₛ , zₜ ⟩ ⊙ x ↔ y ⊙ n) ∎
... | less zₜ-y-1 | yzp =
  xs ⊙⟨ y , zₜ-y-1 ⟩ ∘⟨ x , zₜ ⟩ ⊙ n ≡⟨ cong (λ e → xs ⊙⟨ y , zₜ-y-1 ⟩ ∘⟨ x , e ⟩ ⊙ n) (sym yzp) ⟩
  xs ⊙⟨ y , zₜ-y-1 ⟩ ∘⟨ x , suc y + zₜ-y-1 ⟩ ⊙ n ≡⟨ cons-swap₃ x y zₜ-y-1 xs n ⟩
  xs ∘⟨ x , suc y + zₜ-y-1 ⟩ ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ x , e ⟩ ⊙ x ↔ y ⊙ n) yzp ⟩
  xs ∘⟨ x  , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ e , zₜ ⟩ ⊙ x ↔ y ⊙ n) x≡zₛ ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ∎
... | greater yz | yzp =
  xs ⊙⟨ zₜ , yz ⟩ ∘⟨ x , zₜ ⟩ ⊙ n ≡⟨ cons-swap₂ x zₜ xs yz n ⟩
  (xs ∘⟨ x , zₜ ⟩ ⊙ x ↔ suc (zₜ + yz) ⊙ n) ≡⟨ cong₂ (λ e₁ e₂ → xs ∘⟨ e₁ , zₜ ⟩ ⊙ x ↔ e₂ ⊙ n) x≡zₛ yzp ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ x ↔ y ⊙ n ∎

⊙↓-hom : ∀ xs n → [ xs ]↓ ⊙ n ≡ xs · n
⊙↓-hom ⟨⟩ n = refl
⊙↓-hom (xs ∘⟨ x , y ⟩) n with compare x y | comparing x y 
... | equal | p =
  [ xs ]↓ ⊙ n ≡⟨ ⊙↓-hom xs n ⟩
  xs · n ≡˘⟨ cong (xs ·_) (swap-id x n) ⟩
  (xs · x ↔ x · n) ≡⟨ cong (λ e → xs · x ↔ e · n) p ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
... | less k | p =
  [ xs ]↓ ⊙⟨ x , k ⟩ ⊙ n ≡⟨ cons-swap x k [ xs ]↓ n ⟩
  ([ xs ]↓ ⊙ x ↔ k ⊙ n) ≡⟨ cong ([ xs ]↓ ⊙_) (⊙-· x k n) ⟩
  ([ xs ]↓ ⊙ x ↔ suc x + k · n) ≡⟨ cong (λ e → [ xs ]↓ ⊙ x ↔ e · n) p ⟩
  ([ xs ]↓ ⊙ x ↔ y · n) ≡⟨ ⊙↓-hom xs (x ↔ y · n) ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
... | greater k | p =
  [ xs ]↓ ⊙⟨ y , k ⟩ ⊙ n ≡⟨ cons-swap y k [ xs ]↓ n ⟩
  ([ xs ]↓ ⊙ y ↔ k ⊙ n) ≡⟨ cong ([ xs ]↓ ⊙_) (⊙-· y k n) ⟩
  ([ xs ]↓ ⊙ y ↔ suc y + k · n) ≡⟨ cong (λ e → [ xs ]↓ ⊙ y ↔ e · n) p ⟩
  ([ xs ]↓ ⊙ y ↔ x · n) ≡⟨ ⊙↓-hom xs (y ↔ x · n) ⟩
  (xs · y ↔ x · n) ≡⟨ cong (xs ·_) (swap-com y x n) ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
