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

⟦_∷_⇓⟧^ : ℕ → (ℕ → ℕ) → ℕ → ℕ
⟦ x ∷ xs ⇓⟧^ a = let a′ = 1𝕓⋯ x ∷ a in a′ + xs (1𝕓∷ a′)

⟦_⇓⟧′ : 𝔹 → ℕ → ℕ
-- ⟦_⇓⟧′ = foldr ⟦_∷_⇓⟧^ (const 0)
⟦ [] ⇓⟧′ = const 0
⟦ x ∷ xs ⇓⟧′ = ⟦ x ∷ ⟦ xs ⇓⟧′ ⇓⟧^

⟦_⇓⟧ : 𝔹 → ℕ
⟦ [] ⇓⟧ = zero
⟦ x ∷ xs ⇓⟧ = let a = 1𝕓⋯ x ∷ 1 in a + ⟦ xs ⇓⟧′ a

open import Path.Reasoning
import Data.Nat.Properties as ℕ

2×-+ : ∀ x → 2× x ≡ x + x
-- 2×-+ x = ℕ.*-comm x 2 ; cong (x +_) (ℕ.+-idʳ x)
2×-+ x = refl

1𝕓-distrib : ∀ n x → 1𝕓⋯ suc n ∷ x ≡ 1𝕓⋯ n ∷ 1𝕓∷ x
1𝕓-distrib zero x = refl
1𝕓-distrib (suc n) x = cong 1𝕓∷_ (1𝕓-distrib n x)

lemma : ∀ x xs → 2× (1𝕓⋯ x ∷ 1) + ⟦ xs ⇓⟧′ (1𝕓⋯ suc x ∷ 1) ≡ (1𝕓⋯ x ∷ 1) + ((1𝕓⋯ x ∷ 1) + ⟦ xs ⇓⟧′ (1𝕓⋯ suc x ∷ 1))
lemma x xs = cong (_+ (⟦ xs ⇓⟧′ (1𝕓⋯ suc x ∷ 1))) (2×-+ (1𝕓⋯ x ∷ 1)) ; ℕ.+-assoc (1𝕓⋯ x ∷ 1) (1𝕓⋯ x ∷ 1) _

lemma₂ : ∀ n x xs → ⟦ x ∷ ⟦ xs ⇓⟧′ ⇓⟧^ (1𝕓∷ n) ≡ ⟦ suc x ∷ ⟦ xs ⇓⟧′ ⇓⟧^ n
lemma₂ n x xs =
  ⟦ x ∷ ⟦ xs ⇓⟧′ ⇓⟧^ (1𝕓∷ n) ≡⟨⟩
  (1𝕓⋯ x ∷ 1𝕓∷ n) + ⟦ xs ⇓⟧′ (1𝕓∷ 1𝕓⋯ x ∷ 1𝕓∷ n) ≡˘⟨ cong₂ _+_ (1𝕓-distrib x n) (cong (⟦ xs ⇓⟧′ ∘ 1𝕓∷_) (1𝕓-distrib x n)) ⟩
  (1𝕓⋯ suc x ∷ n) + ⟦ xs ⇓⟧′ (1𝕓∷ 1𝕓⋯ suc x ∷ n) ≡⟨⟩
  ⟦ suc x ∷ ⟦ xs ⇓⟧′ ⇓⟧^ n ∎


inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-suc []                 = refl
inc-suc (x  ∷ [])          = refl
inc-suc (x  ∷ zero   ∷ xs) = cong suc (lemma x xs)
inc-suc (x₁ ∷ suc x₂ ∷ xs) = cong suc (cong ((1𝕓⋯ x₁ ∷ 1) +_) (lemma₂ (1𝕓⋯ x₁ ∷ 1) x₂ xs ))

𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
𝔹-rightInv zero = refl
𝔹-rightInv (suc x) = inc-suc ⟦ x ⇑⟧ ; cong suc (𝔹-rightInv x)

-- 𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
-- 𝔹-leftInv [] = refl
-- 𝔹-leftInv (x ∷ xs) = {!!}

-- 𝔹⇔ℕ : 𝔹 ⇔ ℕ
-- 𝔹⇔ℕ .fun = ⟦_⇓⟧
-- 𝔹⇔ℕ .inv = ⟦_⇑⟧
-- 𝔹⇔ℕ .rightInv x = {!!}
-- 𝔹⇔ℕ .leftInv = {!!}
