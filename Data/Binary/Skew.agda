{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Binary.Skew where

open import Prelude
open import Data.Nat
open import Data.List

𝔹 : Type₀
𝔹 = List ℕ

inc : 𝔹 → 𝔹
inc [] = zero ∷ []
inc (x ∷ []) = zero ∷ x ∷ []
inc (x₁ ∷ zero ∷ xs) = suc x₁ ∷ xs
inc (x₁ ∷ suc x₂ ∷ xs) = zero ∷ x₁ ∷ x₂ ∷ xs

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = []
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

skew : ℕ → ℕ
-- skew n = 1 + (2 * n)
-- Maybe easier for proofs:
skew n = suc (n + n)

w : ℕ → ℕ → ℕ
w zero    a = a
w (suc n) a = skew (w n a)

⟦_⇓⟧′ : 𝔹 → ℕ → ℕ
⟦ []     ⇓⟧′ a = zero
⟦ x ∷ xs ⇓⟧′ a = let a′ = w x a in a′ + ⟦ xs ⇓⟧′ (skew a′)
-- ⟦_⇓⟧′ = foldr f (λ _ → zero)
--   where
--   f : ℕ → (ℕ → ℕ) → ℕ → ℕ
--   f x xs a = let a′ = w x a in a′ + xs (skew a′)

⟦_⇓⟧ : 𝔹 → ℕ
⟦ [] ⇓⟧ = zero
⟦ x ∷ xs ⇓⟧ = let a = w x 1 in a + ⟦ xs ⇓⟧′ a

-- fn : ℕ → _
-- fn n = ⟦ ⟦ n ⇑⟧ ⇓⟧

-- open import Path.Reasoning
-- import Data.Nat.Properties as ℕ

-- inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
-- inc-suc [] = refl
-- inc-suc (x  ∷ []) = refl
-- inc-suc (x  ∷ zero   ∷ xs) = cong suc (ℕ.+-assoc (w x 1) (w x 1) _)
-- inc-suc (x₁ ∷ suc x₂ ∷ xs) = cong suc (cong (w x₁ 1 +_) {!!})

-- 𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
-- 𝔹-rightInv zero = refl
-- 𝔹-rightInv (suc x) = {!!}

-- 𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
-- 𝔹-leftInv [] = refl
-- 𝔹-leftInv (x ∷ xs) = {!!}

-- 𝔹⇔ℕ : 𝔹 ⇔ ℕ
-- 𝔹⇔ℕ .fun = ⟦_⇓⟧
-- 𝔹⇔ℕ .inv = ⟦_⇑⟧
-- 𝔹⇔ℕ .rightInv x = {!!}
-- 𝔹⇔ℕ .leftInv = {!!}
