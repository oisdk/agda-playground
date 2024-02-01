{-# OPTIONS --safe #-}

module Data.Permutation.Normalised.Definition where

open import Prelude hiding (_↔_)
open import Data.List hiding ([]; _∷_)
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Permutation.Swap _≟_
open import Data.Permutation.NonNorm _≟_
open import Data.Nat using (_+_)

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
-- Lemmas
--------------------------------------------------------------------------------

swap-suc : ∀ x y z → suc x ↔ suc y · suc z ≡ suc (x ↔ y · z)
swap-suc = swap-cong (suc , λ _ _ → suc-inj) 

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

shift-0 : ∀ xs → xs ⊙+ 0 ≡ xs
shift-0 ⟨⟩ = refl
shift-0 (_ ∘⟨ _ ⟩) = refl

⊙-alg-dup : ∀ x y z → x ↔ y ⊙ x ↔ y ⊙ z ≡ z
⊙-alg-dup zero y zero = cong (bool′ _ _) (it-does (y ≟ y) refl)
⊙-alg-dup (suc x) y zero = refl
⊙-alg-dup (suc x) y (suc z) = cong suc (⊙-alg-dup x y z)
⊙-alg-dup zero y (suc z) with does (y ≟ z) | why (y ≟ z)
... | true  | y≡z = cong suc y≡z
... | false | y≢z = cong (bool′ _ _) (it-doesn't (y ≟ z) y≢z)

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

⊙-lhs : ∀ x y xs z → y ≢ z → xs ∘⟨ x , y ⟩ ⊙ suc x + z ≡ suc x + (xs ⊙ z)
⊙-lhs (suc x) y xs z y≢z = cong suc (⊙-lhs x y xs z y≢z)
⊙-lhs zero    y xs z y≢z = cong (bool′ _ _) (it-doesn't (y ≟ z) y≢z)

⊙-rhs : ∀ x y xs → xs ∘⟨ x , y ⟩ ⊙ suc x + y ≡ x
⊙-rhs (suc x) y xs = cong suc (⊙-rhs x y xs)
⊙-rhs zero    y xs = cong (bool′ _ _) (it-does (y ≟ y) refl)

supp : Diffs → List ℕ
supp = foldr (λ { (x , y) xs → map (suc x +_) (xs ∘⟨ y ⟩) ∘⟨ x ⟩ }) ⟨⟩

max-num-alg : ℕ × ℕ → ℕ → ℕ
max-num-alg (x , y) z = suc x + (y ⊔ z)

max-num : Diffs → ℕ
max-num = foldr max-num-alg zero

disp-diffs : Diffs → List ℕ
disp-diffs d = map (d ⊙_) (0 ⋯ max-num d)

max-swaps : Swaps → ℕ
max-swaps = foldr (λ { (x , y) z → x ⊔ y ⊔ z }) zero

disp-swaps : Swaps → List ℕ
disp-swaps d = map (d ·_) (0 ⋯ max-swaps d)
