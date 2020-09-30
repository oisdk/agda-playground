{-# OPTIONS --cubical --safe #-}

module Data.Binary.Addition.Properties where

open import Prelude
open import Data.Binary.Definition
open import Data.Binary.Addition
open import Data.Binary.Conversion
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Path.Reasoning
open import Data.Binary.Isomorphism


+-cong : ∀ xs ys → ⟦ xs + ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧
add₁-cong : ∀ xs ys → ⟦ add₁ xs ys ⇓⟧ ≡ 1 ℕ.+ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧
add₂-cong : ∀ xs ys → ⟦ add₂ xs ys ⇓⟧ ≡ 2 ℕ.+ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧

lemma₁ : ∀ xs ys → ⟦ add₁ xs ys ⇓⟧ ℕ.* 2 ≡ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ (2 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2)
lemma₁ xs ys =
  ⟦ add₁ xs ys ⇓⟧ ℕ.* 2 ≡⟨ cong (ℕ._* 2) (add₁-cong xs ys) ⟩
  2 ℕ.+ (⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧) ℕ.* 2 ≡⟨ cong (2 ℕ.+_ ) (ℕ.+-*-distrib ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ 2) ⟩
  2 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2 ≡⟨ cong (ℕ._+ (⟦ ys ⇓⟧ ℕ.* 2)) (ℕ.+-comm 2 (⟦ xs ⇓⟧ ℕ.* 2)) ⟩
  ⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ 2 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2 ≡⟨ ℕ.+-assoc (⟦ xs ⇓⟧ ℕ.* 2) 2 (⟦ ys ⇓⟧ ℕ.* 2) ⟩
  ⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ (2 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2) ∎

lemma₂ : ∀ xs ys → ⟦ add₁ xs ys ⇓⟧ ℕ.* 2 ≡ (1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2) ℕ.+ (1 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2)
lemma₂ xs ys =
  ⟦ add₁ xs ys ⇓⟧ ℕ.* 2 ≡⟨ cong (ℕ._* 2) (add₁-cong xs ys) ⟩
  (1 ℕ.+ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧) ℕ.* 2 ≡⟨ ℕ.+-*-distrib (1 ℕ.+ ⟦ xs ⇓⟧) ⟦ ys ⇓⟧ 2 ⟩
  2 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2 ≡˘⟨ ℕ.+-suc (1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2) (⟦ ys ⇓⟧ ℕ.* 2) ⟩
  (1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2) ℕ.+ (1 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2) ∎

lemma₃ : ∀ xs ys → ⟦ add₂ xs ys ⇓⟧ ℕ.* 2 ≡ suc (suc (⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ suc (suc (⟦ ys ⇓⟧ ℕ.* 2))))
lemma₃ xs ys =
  ⟦ add₂ xs ys ⇓⟧ ℕ.* 2 ≡⟨ cong (ℕ._* 2) (add₂-cong xs ys) ⟩
  (2 ℕ.+ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧) ℕ.* 2 ≡˘⟨ cong (ℕ._* 2) (ℕ.+-suc (1 ℕ.+ ⟦ xs ⇓⟧) ⟦ ys ⇓⟧) ⟩
  ((1 ℕ.+ ⟦ xs ⇓⟧) ℕ.+ (1 ℕ.+ ⟦ ys ⇓⟧)) ℕ.* 2 ≡⟨ ℕ.+-*-distrib (1 ℕ.+ ⟦ xs ⇓⟧) (1 ℕ.+ ⟦ ys ⇓⟧) 2 ⟩
  suc (suc (⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ suc (suc (⟦ ys ⇓⟧ ℕ.* 2)))) ∎

add₁-cong 0ᵇ ys = inc-suc ys
add₁-cong (1ᵇ xs) 0ᵇ = cong (2 ℕ.+_) (sym (ℕ.+-idʳ (⟦ xs ⇓⟧ ℕ.* 2)))
add₁-cong (2ᵇ xs) 0ᵇ = cong suc (cong (ℕ._* 2) (inc-suc xs) ; cong (2 ℕ.+_) (sym (ℕ.+-idʳ (⟦ xs ⇓⟧ ℕ.* 2))))
add₁-cong (1ᵇ xs) (1ᵇ ys) = cong suc (lemma₂ xs ys)
add₁-cong (1ᵇ xs) (2ᵇ ys) = cong (2 ℕ.+_) (lemma₁ xs ys)
add₁-cong (2ᵇ xs) (1ᵇ ys) = cong (2 ℕ.+_) (lemma₂ xs ys)
add₁-cong (2ᵇ xs) (2ᵇ ys) = cong (1 ℕ.+_) (lemma₃ xs ys)

add₂-cong 0ᵇ 0ᵇ = refl
add₂-cong 0ᵇ (1ᵇ ys) = cong (1 ℕ.+_) (cong (ℕ._* 2) (inc-suc ys))
add₂-cong 0ᵇ (2ᵇ ys) = cong (2 ℕ.+_) (cong (ℕ._* 2) (inc-suc ys))
add₂-cong (1ᵇ xs) 0ᵇ = cong (1 ℕ.+_) ((cong (ℕ._* 2) (inc-suc xs)) ; cong (2 ℕ.+_) (sym (ℕ.+-idʳ _)))
add₂-cong (2ᵇ xs) 0ᵇ = cong (2 ℕ.+_) ((cong (ℕ._* 2) (inc-suc xs)) ; cong (2 ℕ.+_) (sym (ℕ.+-idʳ _)))
add₂-cong (1ᵇ xs) (1ᵇ ys) = cong (2 ℕ.+_ ) (lemma₂ xs ys)
add₂-cong (1ᵇ xs) (2ᵇ ys) = cong (1 ℕ.+_) (lemma₃ xs ys)
add₂-cong (2ᵇ xs) (1ᵇ ys) = cong (1 ℕ.+_) (lemma₃ xs ys ; ℕ.+-suc (2 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2) (1 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2))
add₂-cong (2ᵇ xs) (2ᵇ ys) = cong (2 ℕ.+_) (lemma₃ xs ys)

+-cong 0ᵇ ys = refl
+-cong (1ᵇ xs) 0ᵇ = cong suc (sym (ℕ.+-idʳ (⟦ xs ⇓⟧ ℕ.* 2)))
+-cong (2ᵇ xs) 0ᵇ = cong (suc ∘ suc) (sym (ℕ.+-idʳ (⟦ xs ⇓⟧ ℕ.* 2)))
+-cong (1ᵇ xs) (1ᵇ ys) =
  2 ℕ.+ ⟦ xs + ys ⇓⟧ ℕ.* 2 ≡⟨ cong (λ xy → 2 ℕ.+ xy ℕ.* 2) (+-cong xs ys) ⟩
  2 ℕ.+ (⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧) ℕ.* 2 ≡⟨ cong (2 ℕ.+_) (ℕ.+-*-distrib ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ 2) ⟩
  2 ℕ.+ (⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2) ≡˘⟨ cong suc (ℕ.+-suc (⟦ xs ⇓⟧ ℕ.* 2) (⟦ ys ⇓⟧ ℕ.* 2)) ⟩
  1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.+ (1 ℕ.+ ⟦ ys ⇓⟧ ℕ.* 2) ∎
+-cong (1ᵇ xs) (2ᵇ ys) = cong suc (lemma₁ xs ys)
+-cong (2ᵇ xs) (1ᵇ ys) = cong suc (lemma₂ xs ys)
+-cong (2ᵇ xs) (2ᵇ ys) = cong (2 ℕ.+_) (lemma₁ xs ys)

-- +-cong˘ : ∀ xs ys → ⟦ xs ℕ.+ ys ⇑⟧ ≡ ⟦ xs ⇑⟧ + ⟦ ys ⇑⟧
-- +-cong˘ = {!!}
