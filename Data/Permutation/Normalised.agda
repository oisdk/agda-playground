{-# OPTIONS --allow-unsolved-metas #-}

module Data.Permutation.Normalised where

open import Prelude hiding (_↔_)
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Data.List.Properties
open import Data.List hiding ([]; _∷_)
open import Data.Permutation.Swap _≟_
open import Data.Permutation.NonNorm _≟_

--------------------------------------------------------------------------------
-- Diffs type
--------------------------------------------------------------------------------

Diffs : Type
Diffs = List (ℕ × ℕ)

--------------------------------------------------------------------------------
-- Applying a normalised permutation
--------------------------------------------------------------------------------

⊙-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
⊙-alg zero    y k zero    = suc (k y)
⊙-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
⊙-alg (suc x) y k zero    = zero
⊙-alg (suc x) y k (suc z) = suc (⊙-alg x y k z)

infixr 4.5 _⊙_
_⊙_ : Diffs → ℕ → ℕ
_⊙_ = foldr (uncurry ⊙-alg) id

infixr 4.5 _↔_⊙_
_↔_⊙_ : ℕ → ℕ → ℕ → ℕ
_↔_⊙_ x y = ⊙-alg x y id

--------------------------------------------------------------------------------
-- Unnormalise a permutation
--------------------------------------------------------------------------------

unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
unflatten-alg x y k n = k (suc n + x) ∘⟨ n + x , suc (n + x + y) ⟩

unflat : Diffs → ℕ → Swaps
unflat = foldr (uncurry unflatten-alg) (const ⟨⟩)

[_]↑ : Diffs → Swaps
[ xs ]↑ = unflat xs 0

--------------------------------------------------------------------------------
-- Support of a permutation
--------------------------------------------------------------------------------

supp : Diffs → List ℕ
supp = foldr (λ { (x , y) xs → map (suc x +_) (xs ∘⟨ y ⟩) ∘⟨ x ⟩ }) ⟨⟩

--------------------------------------------------------------------------------
-- Unnormalise Proof
--------------------------------------------------------------------------------

swap-suc : ∀ x y z → suc x ↔ suc y · suc z ≡ suc (x ↔ y · z)
swap-suc x y z with does (x ≟ z)
... | true = refl
... | false with does (y ≟ z)
... | false = refl
... | true = refl

⊙-· : ∀ x y z → x ↔ y ⊙ z ≡ x ↔ suc x + y · z
⊙-· (suc x) y (suc z) = cong suc (⊙-· x y z) ; sym (swap-suc x (suc (x + y)) z)
⊙-· (suc x) y zero    = refl
⊙-· zero    y zero    = refl
⊙-· zero    y (suc z) = refl

infixl 5 _⊙+_
_⊙+_ : Diffs → ℕ → Diffs
⟨⟩ ⊙+ _ = ⟨⟩
xs ∘⟨ x , y ⟩ ⊙+ m = xs ∘⟨ m + x , y ⟩

⊙-alg-com : ∀ x y xs z → xs ∘⟨ x , y ⟩ ⊙ z ≡ xs ⊙+ suc x ⊙ x ↔ y ⊙ z
⊙-alg-com x y ⟨⟩ z = refl
⊙-alg-com zero y (xs ∘⟨ w ⟩) zero = refl
⊙-alg-com (suc x) y (xs ∘⟨ w ⟩) zero = refl
⊙-alg-com (suc x) y (xs ∘⟨ w ⟩) (suc z) = cong suc (⊙-alg-com x y (xs ∘⟨ w ⟩) z)
⊙-alg-com zero y (xs ∘⟨ w ⟩) (suc z) with does (y ≟ z)
... | false = refl
... | true  = refl

swap-unf-alg : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
swap-unf-alg x y k m n = k (suc m + x) (m + x ↔ suc (m + x + y) · n)

swap-shift : ∀ m n xs → xs ⊙+ m ⊙ n ≡ foldr (uncurry swap-unf-alg) (const id) xs m n
swap-shift m n ⟨⟩ = refl
swap-shift m n (xs ∘⟨ x , y ⟩) =
  ⊙-alg (m + x) y (xs ⊙_) n
    ≡⟨ ⊙-alg-com (m + x) y xs n ⟩
  (xs ⊙+ suc m + x ⊙ m + x ↔ y ⊙ n)
    ≡⟨ cong (xs ⊙+ suc m + x ⊙_) (⊙-· (m + x) y n) ⟩
  xs ⊙+ suc m + x ⊙ m + x ↔ suc m + x + y · n
    ≡⟨ swap-shift (suc m + x) _ xs ⟩
  swap-unf-alg x y (foldr (uncurry swap-unf-alg) (const id) xs) m n ∎

shift-0 : ∀ xs → xs ⊙+ 0 ≡ xs
shift-0 ⟨⟩ = refl
shift-0 (xs ∘⟨ w ⟩) = refl

swaps-compress : ∀ xs n → xs ⊙ n ≡ [ xs ]↑ · n
swaps-compress xs n =
  xs ⊙ n
    ≡˘⟨ cong (_⊙ n) (shift-0 xs) ⟩
  xs ⊙+ 0 ⊙ n
    ≡⟨ swap-shift 0 n xs ⟩
  foldr (uncurry swap-unf-alg) (const id) xs 0 n
    ≡˘⟨ cong′ {A = ℕ → ℕ → ℕ} (λ e → e 0 n) (foldr-fusion (λ xs m n → foldl-by-r (flip (uncurry _↔_·_)) n (xs m)) (const ⟨⟩) (λ _ _ → refl) xs) ⟩
  foldl-by-r (flip (uncurry _↔_·_)) n [ xs ]↑
    ≡˘⟨ foldl-is-foldr (flip (uncurry _↔_·_)) n [ xs ]↑ ⟩
  [ xs ]↑ · n ∎
  
--------------------------------------------------------------------------------
-- Find range of permutatiuon 
--------------------------------------------------------------------------------

max-num-alg : ℕ × ℕ → ℕ → ℕ
max-num-alg (x , y) z = suc (x + (y ⊔ z))

max-num : Diffs → ℕ
max-num = foldr max-num-alg zero

disp-diffs : Diffs → List ℕ
disp-diffs d = map (d ⊙_) (0 ⋯ max-num d)

max-swaps : Swaps → ℕ
max-swaps = foldr (λ { (x , y) z → x ⊔ y ⊔ z }) zero

disp-swaps : Swaps → List ℕ
disp-swaps d = map (d ·_) (0 ⋯ max-swaps d)

--------------------------------------------------------------------------------
-- Normalise a permutation
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Normalisation proof
--------------------------------------------------------------------------------

⊙-alg-dup : ∀ x y z → x ↔ y ⊙ x ↔ y ⊙ z ≡ z
⊙-alg-dup zero y zero = cong (bool′ _ _) (it-does (y ≟ y) refl)
⊙-alg-dup (suc x) y zero = refl
⊙-alg-dup (suc x) y (suc z) = cong suc (⊙-alg-dup x y z)
⊙-alg-dup zero y (suc z) with does (y ≟ z) | why (y ≟ z)
... | true  | y≡z = cong suc y≡z
... | false | y≢z = cong (bool′ _ _) (it-doesn't (y ≟ z) y≢z)

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

norm-correct : ∀ xs n → [ xs ]↓ ⊙ n ≡ xs · n
norm-correct ⟨⟩ n = refl
norm-correct (xs ∘⟨ x , y ⟩) n with compare x y | comparing x y 
... | equal | p =
  [ xs ]↓ ⊙ n ≡⟨ norm-correct xs n ⟩
  xs · n ≡˘⟨ cong (xs ·_) (swap-id x n) ⟩
  (xs · x ↔ x · n) ≡⟨ cong (λ e → xs · x ↔ e · n) p ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
... | less k | p =
  [ xs ]↓ ⊙⟨ x , k ⟩ ⊙ n ≡⟨ cons-swap x k [ xs ]↓ n ⟩
  ([ xs ]↓ ⊙ x ↔ k ⊙ n) ≡⟨ cong ([ xs ]↓ ⊙_) (⊙-· x k n) ⟩
  ([ xs ]↓ ⊙ x ↔ suc x + k · n) ≡⟨ cong (λ e → [ xs ]↓ ⊙ x ↔ e · n) p ⟩
  ([ xs ]↓ ⊙ x ↔ y · n) ≡⟨ norm-correct xs (x ↔ y · n) ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
... | greater k | p =
  [ xs ]↓ ⊙⟨ y , k ⟩ ⊙ n ≡⟨ cons-swap y k [ xs ]↓ n ⟩
  ([ xs ]↓ ⊙ y ↔ k ⊙ n) ≡⟨ cong ([ xs ]↓ ⊙_) (⊙-· y k n) ⟩
  ([ xs ]↓ ⊙ y ↔ suc y + k · n) ≡⟨ cong (λ e → [ xs ]↓ ⊙ y ↔ e · n) p ⟩
  ([ xs ]↓ ⊙ y ↔ x · n) ≡⟨ norm-correct xs (y ↔ x · n) ⟩
  (xs · y ↔ x · n) ≡⟨ cong (xs ·_) (swap-com y x n) ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎

--------------------------------------------------------------------------------
-- Inversion
--------------------------------------------------------------------------------

⊙-lhs-neq : ∀ x y xs → xs ∘⟨ x , y ⟩ ⊙ x ≢ x
⊙-lhs-neq zero y xs p = snotz p
⊙-lhs-neq (suc x) y xs p = ⊙-lhs-neq x y xs (suc-inj p)

⊙-lt : ∀ xs n → xs ⊙+ suc n ⊙ n ≡ n
⊙-lt ⟨⟩ n = refl
⊙-lt (xs ∘⟨ x , y ⟩) zero = refl
⊙-lt (xs ∘⟨ x , y ⟩) (suc n) = cong suc (⊙-lt (xs ∘⟨ x , y ⟩) n)

⊙+⊙ : ∀ x y xs → xs ⊙+ x ⊙ x + y ≡ x + (xs ⊙ y)
⊙+⊙ x y ⟨⟩ = refl
⊙+⊙ zero y (xs ∘⟨ w , z ⟩) = refl
⊙+⊙ (suc x) y (xs ∘⟨ w , z ⟩) = cong suc (⊙+⊙ x y (xs ∘⟨ w , z ⟩))

step-lemma : ∀ x y xs ys → (∀ n → xs ∘⟨ x , y ⟩ ⊙ n ≡ ys ∘⟨ x , y ⟩ ⊙ n) → ∀ n → xs ⊙ n ≡ ys ⊙ n
step-lemma x y xs ys p n with y ≟ n 
... | no y≢n =
  let h =
        sym (cong (λ e → xs ⊙+ suc x ⊙ e) (swap-neq x (suc x + y) (suc x + n) (x≢sx+y x n) (y≢n ∘ +-inj (suc x)))
        ; ⊙+⊙ (suc x) _ xs)
        ; sym (⊙-alg-com x y xs (suc x + n) ; cong′ {A = ℕ} (λ e → xs ⊙+ suc x ⊙ e) (⊙-· x y (suc (x + n))))
        ; p (suc x + n)
        ; ⊙-alg-com x y ys (suc x + n) ; cong′ {A = ℕ} (λ e → ys ⊙+ suc x ⊙ e) (⊙-· x y (suc (x + n)))
        ; cong (λ e → ys ⊙+ suc x ⊙ e) (swap-neq x (suc x + y) (suc x + n) (x≢sx+y x n) (y≢n ∘ +-inj (suc x)))
        ; ⊙+⊙ (suc x) _ ys
  in +-inj (suc x) h
... | yes y≡n =
  let h = sym (⊙-alg-com x y xs x ; cong (λ e → xs ⊙+ suc x ⊙ e) (⊙-· x y x ; swap-lhs x _) ; ⊙+⊙ (suc x) y xs)
        ; p x
        ; ⊙-alg-com x y ys x ; cong (λ e → ys ⊙+ suc x ⊙ e) (⊙-· x y x ; swap-lhs x _) ; ⊙+⊙ (suc x) y ys
  in  cong (xs ⊙_) (sym y≡n) ; +-inj (suc x) h ; cong (ys ⊙_) y≡n


⊙-inj : ∀ xs n m → xs ⊙ n ≡ xs ⊙ m → n ≡ m
⊙-inj xs n m p = perm-inj [ xs ]↑ n m (sym (swaps-compress xs n) ; p ; swaps-compress xs m)

⊙-lhs : ∀ x y xs z → y ≢ z → xs ∘⟨ x , y ⟩ ⊙ suc x + z ≡ suc x + (xs ⊙ z)
⊙-lhs (suc x) y xs z y≢z = cong suc (⊙-lhs x y xs z y≢z)
⊙-lhs zero    y xs z y≢z = cong (bool′ _ _) (it-doesn't (y ≟ z) y≢z)

⊙-rhs′ : ∀ x y xs → xs ∘⟨ x , y ⟩ ⊙ suc x + y ≡ x
⊙-rhs′ (suc x) y xs = cong suc (⊙-rhs′ x y xs)
⊙-rhs′ zero    y xs = cong (bool′ _ _) (it-does (y ≟ y) refl)

⊙-rhs : ∀ x y xs → xs ∘⟨ x , y ⟩ ⊙ x ≡ suc x + (xs ⊙ y)
⊙-rhs zero y xs = refl
⊙-rhs (suc x) y xs = cong suc (⊙-rhs x y xs)

inj-⊙-lemma : ∀ x xₜ yₜ xs ys
            → (∀ n → xs ∘⟨ x , xₜ ⟩ ⊙ n ≡ ys ∘⟨ x , yₜ ⟩ ⊙ n)
            → xₜ ≢ yₜ
            → xs ⊙ xₜ ≡ ys ⊙ yₜ
            → ∀ n
            → xs ⊙ n ≡ ys ⊙ n
inj-⊙-lemma x xₜ yₜ xs ys p xₜ≢yₜ xye n with n ≟ xₜ | n ≟ yₜ
... | yes n≡xₜ | yes n≡yₜ = ⊥-elim (xₜ≢yₜ (sym n≡xₜ ; n≡yₜ))
... | no  n≢xₜ | yes n≡yₜ =
  ⊥-elim (x≢sx+y x (xs ⊙ n) (sym (sym (⊙-lhs x xₜ xs n (n≢xₜ ∘ sym)) ; p (suc x + n) ; cong (λ e → ys ∘⟨ x , yₜ ⟩ ⊙ suc x + e) n≡yₜ  ; ⊙-rhs′ x yₜ ys)))
... | yes n≡xₜ | no  n≢yₜ =
  ⊥-elim (x≢sx+y x (ys ⊙ n)
    ( sym (⊙-rhs′ x xₜ xs)
    ; cong (λ e → xs ∘⟨ x , xₜ ⟩ ⊙ suc x + e) (sym n≡xₜ)
    ; p (suc x + n)
    ; ⊙-lhs x yₜ ys n (n≢yₜ ∘ sym)
    ))
... | no  n≢xₜ | no  n≢yₜ =
  +-inj (suc x) (sym (⊙-lhs x xₜ xs n (n≢xₜ ∘ sym)) ; p (suc x + n) ; ⊙-lhs x yₜ ys n (n≢yₜ ∘ sym))

inj-⊙ : ∀ xs ys → (∀ n → xs ⊙ n ≡ ys ⊙ n) → xs ≡ ys
inj-⊙ ⟨⟩ ⟨⟩ _ = refl
inj-⊙ ⟨⟩ (ys ∘⟨ x , y ⟩) p = ⊥-elim (⊙-lhs-neq x y ys (sym (p x)))
inj-⊙ (xs ∘⟨ x , y ⟩) ⟨⟩ p = ⊥-elim (⊙-lhs-neq x y xs (p x))
inj-⊙ (xs ∘⟨ xₛ , xₜ ⟩) (ys ∘⟨ yₛ , yₜ ⟩) p with xₛ ≟ yₛ | xₜ ≟ yₜ

... | yes xₛ≡yₛ | yes xₜ≡yₜ = cong₂ _∘⟨_⟩ (inj-⊙ xs ys  λ n → step-lemma xₛ xₜ xs ys (_; cong₂ (λ e₁ e₂ → ys ∘⟨ e₁ , e₂ ⟩ ⊙ _) (sym xₛ≡yₛ) (sym xₜ≡yₜ) ∘ p) n ) (cong₂ _,_ xₛ≡yₛ xₜ≡yₜ)
... | yes xₛ≡yₛ | no xₜ≢yₜ =
  let h = +-inj (suc xₛ) $ sym (⊙-alg-com xₛ xₜ xs xₛ ; cong (λ e → xs ⊙+ suc xₛ ⊙ e) (⊙-· xₛ xₜ xₛ ; swap-lhs xₛ _) ; ⊙+⊙ (suc xₛ) xₜ xs)
        ; p xₛ
        ; cong (ys ∘⟨ yₛ , yₜ ⟩ ⊙_) xₛ≡yₛ
        ; ⊙-alg-com yₛ yₜ ys yₛ ; cong (λ e → ys ⊙+ suc yₛ ⊙ e) (⊙-· yₛ yₜ yₛ ; swap-lhs yₛ _) ; ⊙+⊙ (suc yₛ) yₜ ys
        ; cong suc (cong (_+ (ys ⊙ yₜ)) (sym xₛ≡yₛ)) 
      h′ = inj-⊙ xs ys (inj-⊙-lemma xₛ xₜ yₜ xs ys ( λ n → p n ; cong (λ e → ys ∘⟨ e , yₜ ⟩ ⊙ n) (sym xₛ≡yₛ) ) xₜ≢yₜ h )
          
      h″ = ⊙-inj xs xₜ yₜ (h ; cong (_⊙ yₜ) (sym h′))
  in ⊥-elim (xₜ≢yₜ h″)
... | no  xₛ≢yₛ | _ with compare xₛ yₛ | comparing xₛ yₛ
... | equal | xₛ≡yₛ = ⊥-elim (xₛ≢yₛ xₛ≡yₛ)
... | less    k | xₛ<yₛ =
  ⊥-elim (⊙-lhs-neq xₛ xₜ xs (p xₛ ; cong (λ e → ys ∘⟨ e , yₜ ⟩ ⊙ xₛ) (sym xₛ<yₛ) ; ⊙-lt (ys ∘⟨ k , yₜ ⟩) xₛ))
... | greater k | yₛ<xₛ =
  ⊥-elim (⊙-lhs-neq yₛ yₜ ys (sym (p yₛ) ; cong (λ e → xs ∘⟨ e , xₜ ⟩ ⊙ yₛ) (sym yₛ<xₛ) ; ⊙-lt (xs ∘⟨ k , xₜ ⟩) yₛ))

unf-coalg : ℕ → ℕ → (ℕ → Diffs) → ℕ → Diffs
unf-coalg x y k n = k (suc n + x) ∘⟨ n + x , y ⟩ 

un-diff : Diffs → ℕ → Diffs
un-diff = foldr (uncurry unf-coalg) (const ⟨⟩)

compare-diff-+ : ∀ x y → compare x (suc x + y) ≡ less y
compare-diff-+ zero y = refl
compare-diff-+ (suc x) y = compare-diff-+ x y

norm-lemma₁ : ∀ xs x y → xs ⊙+ suc x ⊙⟨ x , y ⟩ ≡ xs ∘⟨ x , y ⟩
norm-lemma₁ ⟨⟩ x y = refl
norm-lemma₁ (xs ∘⟨ s , t ⟩) x y with compare x (suc x + s) | comparing x (suc x + s)
... | less    k | sx+k≡sx+s = cong (λ e → xs ∘⟨ e , t ⟩ ∘⟨ x , y ⟩) (+-inj (suc x) sx+k≡sx+s)
... | equal     | x≡sx+s = ⊥-elim (x≢sx+y x s x≡sx+s)
... | greater k | p = ⊥-elim (x≢sx+y x (suc s + k) (sym p ; cong suc (cong suc (+-assoc x s k) ; sym (+-suc x (s + k)))))

norm-lemma : ∀ xs n → foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs n) ≡ xs ⊙+ n
norm-lemma ⟨⟩ n = refl
norm-lemma (xs ∘⟨ x , y ⟩) n =
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff (xs ∘⟨ x , y ⟩) n) ≡⟨⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs (suc n + x) ∘⟨ n + x , y ⟩) ≡⟨⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs (suc n + x)) ⊙⟨ n + x , y ⟩ ≡⟨ cong (_⊙⟨ n + x , y ⟩) (norm-lemma xs (suc n + x)) ⟩
  xs ⊙+ suc n + x ⊙⟨ n + x , y ⟩ ≡⟨ norm-lemma₁ xs (n + x) y ⟩
  xs ∘⟨ n + x , y ⟩ ∎

norm-inv : ∀ xs → [ [ xs ]↑ ]↓ ≡ xs
norm-inv xs =
  [ [ xs ]↑ ]↓ ≡⟨⟩
  [ foldr (uncurry unflatten-alg) (const ⟨⟩) xs 0 ]↓ ≡⟨⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (catMaybes (uncurry swap-diff) (foldr (uncurry unflatten-alg) (const ⟨⟩) xs 0))
    ≡⟨ cong′ {A = ℕ → Swaps} (λ k → foldr (flip _⊙⟨_⟩) ⟨⟩ (k 0)) (foldr-fusion (λ xs n → catMaybes (uncurry swap-diff) (xs n)) (const ⟨⟩) (λ { (x , y) k → funExt λ n → cong (maybe _ _) (cong (mapMaybe (map₁ (bool′ (n + x) _))) (compare-diff-+ (n + x) y)) }) xs) ⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs 0)
    ≡⟨  norm-lemma xs 0 ⟩
  xs ⊙+ 0
    ≡⟨ shift-0 xs ⟩
  xs ∎

--------------------------------------------------------------------------------
-- Group Operator
--------------------------------------------------------------------------------

⊕-from : Diffs → Diffs → ℕ → Diffs
⊕-from xs ys n = foldr (flip _⊙⟨_⟩) xs (un-diff ys n)

infixl 6 _⊕_
_⊕_ : Diffs → Diffs → Diffs
xs ⊕ ys = ⊕-from xs ys 0

diffs-comp-lemma : ∀ xs ys m n → foldr (flip _⊙⟨_⟩) xs (un-diff ys m) ⊙ n ≡ xs ⊙ (ys ⊙+ m ⊙ n)
diffs-comp-lemma xs ⟨⟩ m n = refl
diffs-comp-lemma xs (ys ∘⟨ x , y ⟩) m n =
  ⊕-from xs (ys ∘⟨ x , y ⟩) m ⊙ n ≡⟨⟩
  ⊕-from xs ys (suc m + x) ⊙⟨ m + x , y ⟩ ⊙ n ≡⟨ cons-swap (m + x) y (⊕-from xs ys (suc m + x)) n ⟩
  ⊕-from xs ys (suc m + x) ⊙ m + x ↔ y ⊙ n ≡⟨ diffs-comp-lemma xs ys (suc m + x) _ ⟩
  (xs ⊙ ys ⊙+ suc m + x ⊙ m + x ↔ y ⊙ n) ≡˘⟨ cong (xs ⊙_) (⊙-alg-com (m + x) y ys n ) ⟩
  (xs ⊙ ys ∘⟨ m + x , y ⟩ ⊙ n) ≡⟨⟩
  (xs ⊙ ys ∘⟨ x , y ⟩ ⊙+ m ⊙ n) ∎

diffs-comp : ∀ xs ys n → (xs ⊕ ys) ⊙ n ≡ xs ⊙ (ys ⊙ n)
diffs-comp xs ys n =
  xs ⊕ ys ⊙ n ≡⟨ diffs-comp-lemma xs ys 0 n  ⟩
  xs ⊙ (ys ⊙+ 0 ⊙ n) ≡⟨ cong (λ e → xs ⊙ e ⊙ n) (shift-0 ys) ⟩
  xs ⊙ ys ⊙ n ∎


-- ⊕-hom : ∀ xs ys → [ xs ∙ ys ]↓ ≡ [ xs ]↓ ⊕ [ ys ]↓
-- ⊕-hom xs ⟨⟩ = refl
-- ⊕-hom xs (ys ∘⟨ x , y ⟩) with compare x y
-- ... | equal = ⊕-hom xs ys
-- ... | greater k = {!!}
-- ... | less k =
--   [ xs ∙ ys ]↓ ⊙⟨ x , k ⟩ ≡⟨ cong (_⊙⟨ x , k ⟩) (⊕-hom xs ys) ⟩
--   ([ xs ]↓ ⊕ [ ys ]↓) ⊙⟨ x , k ⟩ ≡⟨ {!!} ⟩
--   [ xs ]↓ ⊕ ([ ys ]↓ ⊙⟨ x , k ⟩) ∎
  
