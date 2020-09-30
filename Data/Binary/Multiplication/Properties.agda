{-# OPTIONS --cubical --safe #-}

module Data.Binary.Multiplication.Properties where

open import Prelude
open import Data.Binary.Definition
open import Data.Binary.Addition
open import Data.Binary.Addition.Properties using (+-cong)
open import Data.Binary.Multiplication
open import Data.Binary.Conversion
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Path.Reasoning
open import Data.Binary.Isomorphism

double-cong : ∀ xs → ⟦ double xs ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* 2
double-cong 0ᵇ i = zero
double-cong (1ᵇ xs) i = 2 ℕ.+ double-cong xs i ℕ.* 2
double-cong (2ᵇ xs) i = ⟦ 2ᵇ 1ᵇ xs ⇓⟧

double-plus : ∀ x → x ℕ.+ x ≡ x ℕ.* 2
double-plus x = cong (x ℕ.+_) (sym (ℕ.+-idʳ x)) ; ℕ.*-comm 2 x

lemma₁ : ∀ x y → x ℕ.* y ℕ.* 2 ≡ y ℕ.* 2 ℕ.* x
lemma₁ x y =
  x ℕ.* y ℕ.* 2 ≡⟨ ℕ.*-assoc x y 2 ⟩
  x ℕ.* (y ℕ.* 2) ≡⟨ ℕ.*-comm x (y ℕ.* 2) ⟩
  y ℕ.* 2 ℕ.* x ∎

lemma₂ : ∀ x y → (x ℕ.+ x ℕ.* y) ℕ.* 2 ≡ x ℕ.+ (x ℕ.+ y ℕ.* 2 ℕ.* x)
lemma₂ x y =
  (x ℕ.+ x ℕ.* y) ℕ.* 2 ≡⟨ ℕ.+-*-distrib x (x ℕ.* y) 2 ⟩
  x ℕ.* 2 ℕ.+ x ℕ.* y ℕ.* 2 ≡⟨ cong₂ ℕ._+_ (sym (double-plus x)) (lemma₁ x y) ⟩
  x ℕ.+ x ℕ.+ y ℕ.* 2 ℕ.* x ≡⟨ ℕ.+-assoc x x (y ℕ.* 2 ℕ.* x) ⟩
  x ℕ.+ (x ℕ.+ y ℕ.* 2 ℕ.* x) ∎

*-cong : ∀ xs ys → ⟦ xs * ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* ⟦ ys ⇓⟧
*-cong 0ᵇ ys = refl
*-cong (1ᵇ xs) ys =
  ⟦ ys + double (ys * xs) ⇓⟧ ≡⟨ +-cong ys (double (ys * xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ double (ys * xs) ⇓⟧ ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_)  (double-cong (ys * xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ ys * xs ⇓⟧ ℕ.* 2 ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_)  (cong (ℕ._* 2) (*-cong ys xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ ys ⇓⟧ ℕ.* ⟦ xs ⇓⟧ ℕ.* 2 ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_) (lemma₁ ⟦ ys ⇓⟧ ⟦ xs ⇓⟧) ⟩
  ⟦ ys ⇓⟧ ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.* ⟦ ys ⇓⟧ ∎
*-cong (2ᵇ xs) ys =
  ⟦ double (ys + ys * xs) ⇓⟧ ≡⟨ double-cong (ys + ys * xs) ⟩
  ⟦ ys + ys * xs ⇓⟧ ℕ.* 2 ≡⟨ cong (ℕ._* 2) (+-cong ys (ys * xs)) ⟩
  (⟦ ys ⇓⟧ ℕ.+ ⟦ ys * xs ⇓⟧) ℕ.* 2 ≡⟨ cong (ℕ._* 2) (cong (⟦ ys ⇓⟧ ℕ.+_) (*-cong ys xs)) ⟩
  (⟦ ys ⇓⟧ ℕ.+ ⟦ ys ⇓⟧ ℕ.* ⟦ xs ⇓⟧) ℕ.* 2 ≡⟨ lemma₂ ⟦ ys ⇓⟧ ⟦ xs ⇓⟧  ⟩
  ⟦ ys ⇓⟧ ℕ.+ (⟦ ys ⇓⟧ ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.* ⟦ ys ⇓⟧) ∎
