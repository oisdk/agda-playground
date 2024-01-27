{-# OPTIONS --allow-unsolved-metas #-}

module Data.Permutation where

open import Prelude
open import Data.List
open import Data.Nat.Properties renaming (discreteℕ to _≟_)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Data.List.Properties

Swaps : Type
Swaps = List (ℕ × ℕ)

unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
unflatten-alg x y k n = ((n + x) , suc (n + x + y)) ∷ k (suc n + x)

unflatten : Swaps → Swaps
unflatten xs = foldr (uncurry unflatten-alg) (const []) xs 0

swap : ℕ → ℕ → ℕ → ℕ
swap x y z =
  if does (x ≟ z) then y else
  if does (y ≟ z) then x else
  z

swap′ : ℕ → ℕ → ℕ → ℕ
swap′ zero zero z = z
swap′ zero y zero = y
swap′ x zero zero = x
swap′ (suc x) (suc y) zero = zero
swap′ (suc x) (suc y) (suc z) = suc (swap′ x y z)
swap′ (suc x) zero (suc z) = if does (x ≟ z) then zero else suc z
swap′ zero (suc y) (suc z) = if does (y ≟ z) then zero else suc z

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

swap-suc : ∀ x y z → swap (suc x) (suc y) (suc z) ≡ suc (swap x y z)
swap-suc x y z with does (x ≟ z)
... | true = refl
... | false with does (y ≟ z)
... | false = refl
... | true = refl

swap-swap′ : ∀ x y z → swap x y z ≡ swap′ x y z
swap-swap′ zero zero zero = refl
swap-swap′ zero zero (suc z) = refl
swap-swap′ zero (suc y) zero = refl
swap-swap′ (suc x) zero zero = refl
swap-swap′ (suc x) (suc y) zero = refl
swap-swap′ (suc x) (suc y) (suc z) = swap-suc x y z ; cong suc (swap-swap′ x y z)
swap-swap′ zero (suc y) (suc z) = refl
swap-swap′ (suc x) zero (suc z) = refl

swap-id : ∀ x y → swap x x y ≡ y
swap-id x y with does (x ≟ y) | why (x ≟ y)
... | false | _ = refl
... | true  | x≡y = x≡y

perm : Swaps → ℕ → ℕ
perm = flip (foldl (flip (uncurry swap)))

ep : Swaps
ep = ((2 , 1) ∷ (1 , 3) ∷ (1 , 0) ∷ [])

perm-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
perm-alg zero    y k zero    = suc (k y)
perm-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
perm-alg (suc x) y k zero    = zero
perm-alg (suc x) y k (suc z) = suc (perm-alg x y k z)

perm′ : Swaps → ℕ → ℕ
perm′ = foldr (uncurry perm-alg) id

prop : (xs : Swaps) (n : ℕ) → Type
prop xs n = perm′ xs n ≡ perm (unflatten xs) n

swap-unf-alg : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
swap-unf-alg x y k a n = k (suc a + x) (swap (a + x) (suc (a + x + y)) n)

swap-unf′ : Swaps → ℕ → ℕ → ℕ
swap-unf′ = foldr (uncurry swap-unf-alg) (const id)

swap-unflatten : Swaps → ℕ → ℕ
swap-unflatten xs = swap-unf′ xs 0

swap-unflatten-lemma : ∀ xs m n → swap-unf′ xs m n ≡ foldr (λ x k xs → k (uncurry swap x xs)) id (foldr (uncurry unflatten-alg) (const []) xs m) n
swap-unflatten-lemma [] m n = refl
swap-unflatten-lemma (x ∷ xs) m n = cong (λ e → uncurry swap-unf-alg x e m n) (funExt λ m → funExt (swap-unflatten-lemma xs m))

open import Data.Nat

swaps-compress : ∀ xs n → perm′ xs n ≡ perm (unflatten xs) n
swaps-compress xs n =
  perm′ xs n
    ≡⟨ {!!} ⟩
  swap-unf′ xs 0 n
    ≡⟨ swap-unflatten-lemma xs 0 n ⟩
  foldr (λ x k xs → k (uncurry swap x xs)) id (foldr (uncurry unflatten-alg) (const []) xs 0) n
    ≡⟨⟩
  foldr (λ x k xs → k (uncurry swap x xs)) id (unflatten xs) n
    ≡˘⟨ foldl-is-foldr (flip (uncurry swap)) n (unflatten xs) ⟩
  foldl (flip (uncurry swap)) n (unflatten xs) ≡⟨⟩
  perm (unflatten xs) n ∎
