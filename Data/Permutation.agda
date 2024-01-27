{-# OPTIONS --allow-unsolved-metas #-}

module Data.Permutation where

open import Prelude
open import Data.List
open import Data.Nat.Properties renaming (discreteℕ to _≟_)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Data.List.Properties

--------------------------------------------------------------------------------
-- Unnormalised Representation
--------------------------------------------------------------------------------

Swaps : Type
Swaps = List (ℕ × ℕ)

swap : ℕ → ℕ → ℕ → ℕ
swap x y z =
  if does (x ≟ z) then y else
  if does (y ≟ z) then x else
  z

swap-lhs : ∀ x y → swap x y x ≡ y
swap-lhs x y with does (x ≟ x) | why (x ≟ x)
... | true  | _ = refl
... | false | x≢x = ⊥-elim (x≢x refl)

swap-rhs : ∀ x y → swap x y y ≡ x
swap-rhs x y with does (x ≟ y) | why (x ≟ y)
... | true  | x≡y = sym x≡y
... | false | _ with does (y ≟ y) | why (y ≟ y)
... | false | y≢y = ⊥-elim (y≢y refl)
... | true  | _ = refl

swap-id : ∀ x y → swap x x y ≡ y
swap-id x y with does (x ≟ y) | why (x ≟ y)
... | false | _ = refl
... | true  | x≡y = x≡y

perm : Swaps → ℕ → ℕ
perm = flip (foldl (flip (uncurry swap)))

--------------------------------------------------------------------------------
-- Normalised Representation
--------------------------------------------------------------------------------

Diffs : Type
Diffs = List (ℕ × ℕ)

unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
unflatten-alg x y k n = ((n + x) , suc (n + x + y)) ∷ k (suc n + x)

unflatten : Diffs → Swaps
unflatten xs = foldr (uncurry unflatten-alg) (const []) xs 0

swap′ : ℕ → ℕ → ℕ → ℕ
swap′ zero zero z = z
swap′ zero y@(suc _) zero = y
swap′ zero (suc y) (suc z) = if does (y ≟ z) then zero else suc z
swap′ x@(suc _) zero zero = x
swap′ (suc x) (suc y) zero = zero
swap′ (suc x) zero (suc z) = if does (x ≟ z) then zero else suc z
swap′ (suc x) (suc y) (suc z) = suc (swap′ x y z)

swap-suc : ∀ x y z → swap (suc x) (suc y) (suc z) ≡ suc (swap x y z)
swap-suc x y z with does (x ≟ z)
... | true = refl
... | false with does (y ≟ z)
... | false = refl
... | true = refl

swap-swap′ : ∀ x y z → swap x y z ≡ swap′ x y z
swap-swap′ zero    zero    z       = swap-id zero z
swap-swap′ zero    (suc y) zero    = refl
swap-swap′ zero    (suc y) (suc z) = refl
swap-swap′ (suc x) zero    zero    = refl
swap-swap′ (suc x) (suc y) zero    = refl
swap-swap′ (suc x) zero    (suc z) = refl
swap-swap′ (suc x) (suc y) (suc z) = swap-suc x y z ; cong suc (swap-swap′ x y z)

perm-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
perm-alg zero    y k zero    = suc (k y)
perm-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
perm-alg (suc x) y k zero    = zero
perm-alg (suc x) y k (suc z) = suc (perm-alg x y k z)

perm′ : Swaps → ℕ → ℕ
perm′ = foldr (uncurry perm-alg) id

perm-alg-swap : ∀ x y z → perm-alg x y id z ≡ swap′ x (suc (x + y)) z
perm-alg-swap zero y zero = refl
perm-alg-swap zero y (suc z) = refl
perm-alg-swap (suc x) y zero = refl
perm-alg-swap (suc x) y (suc z) = cong suc (perm-alg-swap x y z)

shift : ℕ → Diffs → Diffs
shift m [] = []
shift m ((x , y) ∷ xs) = (m + x , y) ∷ xs

perm-alg-com : ∀ x y xs z → perm-alg x y (perm′ xs) z ≡ perm′ (shift (suc x) xs) (perm-alg x y id z)
perm-alg-com x y [] z = refl
perm-alg-com zero y (w ∷ xs) zero = refl
perm-alg-com (suc x) y (w ∷ xs) zero = refl
perm-alg-com (suc x) y (w ∷ xs) (suc z) = cong suc (perm-alg-com x y (w ∷ xs) z)
perm-alg-com zero y (w ∷ xs) (suc z) with does (y ≟ z)
... | false = refl
... | true  = refl

swap-unf-alg : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
swap-unf-alg x y k m n = k (suc m + x) (swap (m + x) (suc (m + x + y)) n)

swap-unf′ : Swaps → ℕ → ℕ → ℕ
swap-unf′ = foldr (uncurry swap-unf-alg) (const id)

swap-shift : ∀ m n xs → perm′ (shift m xs) n ≡ swap-unf′ xs m n
swap-shift m n [] = refl
swap-shift m n ((x , y) ∷ xs) =
  perm-alg (m + x) y (perm′ xs) n
    ≡⟨ perm-alg-com (m + x) y xs n ⟩
  perm′ (shift (suc m + x) xs) (perm-alg (m + x) y id n)
    ≡⟨ cong (perm′ (shift (suc m + x) xs)) (perm-alg-swap (m + x) y n) ⟩
  perm′ (shift (suc m + x) xs) (swap′ (m + x) (suc (m + x + y)) n)
    ≡˘⟨ cong (perm′ (shift (suc m + x) xs)) (swap-swap′ (m + x) _ n) ⟩
  perm′ (shift (suc m + x) xs) (swap (m + x) (suc (m + x + y)) n)
    ≡⟨ swap-shift (suc m + x) _ xs ⟩
  swap-unf′ xs (suc m + x) (swap (m + x) (suc (m + x + y)) n)
    ≡⟨⟩
  swap-unf-alg x y (swap-unf′ xs) m n ∎

shift-0 : ∀ xs → shift 0 xs ≡ xs
shift-0 [] = refl
shift-0 (x ∷ xs) = refl

swaps-compress : ∀ xs n → perm′ xs n ≡ perm (unflatten xs) n
swaps-compress xs n =
  perm′ xs n
    ≡˘⟨ cong (flip perm′ n) (shift-0 xs) ⟩
  perm′ (shift 0 xs) n
    ≡⟨ swap-shift 0 n xs ⟩
  swap-unf′ xs 0 n
    ≡˘⟨ cong′ {A = ℕ → ℕ → ℕ} (λ e → e 0 n) (foldr-fusion (λ xs m n → foldl-by-r (flip (uncurry swap)) n (xs m)) (const []) (λ _ _ → refl) xs) ⟩
  foldl-by-r (flip (uncurry swap)) n (unflatten xs)
    ≡˘⟨ foldl-is-foldr (flip (uncurry swap)) n (unflatten xs) ⟩
  perm (unflatten xs) n ∎
  
max-num-alg : ℕ × ℕ → ℕ → ℕ
max-num-alg (x , y) z = suc (x + (y ⊔ z))

max-num : Swaps → ℕ
max-num = foldr max-num-alg zero
