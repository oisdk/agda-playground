{-# OPTIONS --safe #-}

module Data.Binary.Skew where

open import Prelude
open import Data.Nat
open import Data.List

𝔹 : Type
𝔹 = List ℕ

inc : 𝔹 → 𝔹
inc [] = zero ∷ []
inc (x ∷ []) = zero ∷ x ∷ []
inc (x₁ ∷ zero   ∷ xs) = suc x₁ ∷ xs
inc (x₁ ∷ suc x₂ ∷ xs) = zero ∷ x₁ ∷ x₂ ∷ xs

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = []
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

2×_ : ℕ → ℕ
2× n = n + n

infixr 5 1𝕓∷_ 1𝕓⋯_∷_
1𝕓∷_ : ℕ → ℕ
1𝕓∷ n = 1 + 2× n

1𝕓⋯_∷_ : ℕ → ℕ → ℕ
1𝕓⋯ zero  ∷ a = a
1𝕓⋯ suc n ∷ a = 1𝕓∷ 1𝕓⋯ n ∷ a

⟦∷_⇓⟧^ : (ℕ → ℕ) → ℕ → ℕ
⟦∷ xs ⇓⟧^ a′ = a′ + xs (1𝕓∷ a′)

⟦_∷_⇓⟧^ : ℕ → (ℕ → ℕ) → ℕ → ℕ
⟦ x ∷ xs ⇓⟧^ a = ⟦∷ xs ⇓⟧^  (1𝕓⋯ x ∷ a)

⟦_⇓⟧′ : 𝔹 → ℕ → ℕ
-- ⟦_⇓⟧′ = foldr ⟦_∷_⇓⟧^ (const 0)
⟦ [] ⇓⟧′ = const 0
⟦ x ∷ xs ⇓⟧′ = ⟦ x ∷ ⟦ xs ⇓⟧′ ⇓⟧^

⟦_⇓⟧ : 𝔹 → ℕ
⟦ [] ⇓⟧     = zero
⟦ x ∷ xs ⇓⟧ = let a = 1𝕓⋯ x ∷ 1 in a + ⟦ xs ⇓⟧′ a

⟦_⇓⟧″ : 𝔹 → ℕ
⟦ [] ⇓⟧″     = zero
⟦ x₁ ∷ [] ⇓⟧″ = 1𝕓⋯ x₁ ∷ 1
⟦ x₁ ∷ zero   ∷ xs ⇓⟧″ = let a = 2× (1𝕓⋯ x₁ ∷ 1) in a + ⟦ xs ⇓⟧′ (suc a)
⟦ x₁ ∷ suc x₂ ∷ xs ⇓⟧″ = ⟦ x₁ ∷ x₂ ∷ xs ⇓⟧′ 1

inc⁺ : ℕ → 𝔹 → ℕ × 𝔹
inc⁺ a []           = a , []
inc⁺ a (0 ∷ xs)     = inc⁺ (suc a) xs
inc⁺ a (suc x ∷ xs) = a , x ∷ xs

inc′ : 𝔹 → 𝔹
inc′ = uncurry _∷_ ∘ inc⁺ 0

⟦_⇑⟧′ : ℕ → ℕ → 𝔹
⟦ zero ⇑⟧′  a = []
⟦ suc n ⇑⟧′ a = inc′ (⟦ n ⇑⟧′ a)

-- open import Testers

-- _ : testIsoℕ⁻ ((flip ⟦_⇑⟧′ 1) iff (flip ⟦_⇓⟧′ 1)) 10
-- _ = refl

open import Path.Reasoning
import Data.Nat.Properties as ℕ

1𝕓-distrib : ∀ n x → 1𝕓⋯ n ∷ 1𝕓∷ x ≡ 1𝕓⋯ suc n ∷ x
1𝕓-distrib zero x = refl
1𝕓-distrib (suc n) x = cong 1𝕓∷_ (1𝕓-distrib n x)

inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-suc []                 = refl
inc-suc (x  ∷ [])          = refl
inc-suc (x  ∷ zero   ∷ xs) = cong suc (ℕ.+-assoc (1𝕓⋯ x ∷ 1) (1𝕓⋯ x ∷ 1) _)
inc-suc (x₁ ∷ suc x₂ ∷ xs) = cong (suc ∘ ((1𝕓⋯ x₁ ∷ 1) +_) ∘ ⟦∷ ⟦ xs ⇓⟧′ ⇓⟧^) (1𝕓-distrib x₂ (1𝕓⋯ x₁ ∷ 1))

𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
𝔹-rightInv zero = refl
𝔹-rightInv (suc x) = inc-suc ⟦ x ⇑⟧ ; cong suc (𝔹-rightInv x)

-- lemma : ∀ x₁ x₂ xs → ⟦ ⟦ x₁ ∷ ⟦ x₂ ∷ ⟦ xs ⇓⟧′ ⇓⟧^ ⇓⟧^ 1 ⇑⟧ ≡ x₁ ∷ suc x₂ ∷ xs
-- lemma x₁ x₂ xs = {!!}

-- 𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧″ ⇑⟧ ≡ x
-- 𝔹-leftInv []       = refl
-- 𝔹-leftInv (x ∷ []) = {!!}
-- 𝔹-leftInv (x₁ ∷ zero ∷ xs) = {!!}
-- 𝔹-leftInv (x₁ ∷ suc x₂ ∷ xs) = {!!}

-- -- inc-2*-1ᵇ : ∀ n → inc ⟦ n ℕ.* 2 ⇑⟧ ≡ 1ᵇ ⟦ n ⇑⟧
-- -- inc-2*-1ᵇ zero    i = 1ᵇ 0ᵇ
-- -- inc-2*-1ᵇ (suc n) i = inc (inc (inc-2*-1ᵇ n i))

-- -- 𝔹⇔ℕ : 𝔹 ⇔ ℕ
-- -- 𝔹⇔ℕ .fun = ⟦_⇓⟧
-- -- 𝔹⇔ℕ .inv = ⟦_⇑⟧
-- -- 𝔹⇔ℕ .rightInv x = {!!}
-- -- 𝔹⇔ℕ .leftInv = {!!}
