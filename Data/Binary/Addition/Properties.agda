{-# OPTIONS --cubical --safe #-}

module Data.Binary.Addition.Properties where

open import Prelude
open import Data.Binary.Definition
open import Data.Binary.Addition
open import Data.Binary.Conversion
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Path.Reasoning

-- +-cong : ∀ xs ys → ⟦ xs + ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧
-- +-cong 0ᵇ ys = refl
-- +-cong (1ᵇ xs) 0ᵇ = cong suc (sym (ℕ.+-idʳ (⟦ xs ⇓⟧ ℕ.* 2)))
-- +-cong (2ᵇ xs) 0ᵇ = cong (suc ∘ suc) (sym (ℕ.+-idʳ (⟦ xs ⇓⟧ ℕ.* 2)))
-- +-cong (1ᵇ xs) (1ᵇ ys) =
--   ⟦ (1ᵇ xs) + (1ᵇ ys) ⇓⟧ ≡⟨⟩
--   ⟦ 2ᵇ xs + ys ⇓⟧ ≡⟨⟩
--   2 ℕ.+ ⟦ xs + ys ⇓⟧ ℕ.* 2 ≡⟨ cong (λ n → suc (suc (n ℕ.* 2))) (+-cong xs ys) ⟩
--   2 ℕ.+ (⟦ xs ⇓⟧ ℕ.+  ⟦ ys ⇓⟧) ℕ.* 2 ≡⟨ {!!} ⟩
--   2 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2 ≡˘⟨ ℕ.+-suc (1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2) (⟦ ys ⇓⟧ ℕ.* 2) ⟩
--   (1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2) ℕ.+ (1 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2) ≡⟨⟩
--   ⟦ 1ᵇ xs ⇓⟧ ℕ.+ ⟦ 1ᵇ ys ⇓⟧ ∎
-- +-cong (1ᵇ xs) (2ᵇ ys) = {!!}
-- +-cong (2ᵇ xs) (1ᵇ ys) = {!!}
-- +-cong (2ᵇ xs) (2ᵇ ys) = {!!}
