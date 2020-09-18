{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Binary.Isomorphism where

open import Data.Binary.Definition
open import Data.Binary.Conversion
open import Data.Binary.Increment
open import Prelude
import Data.Nat as ℕ

inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-suc []      i = 1
inc-suc (1ᵇ∷ x) i = ⟦ 2ᵇ∷ x ⇓⟧
inc-suc (2ᵇ∷ x) i = suc (inc-suc x i ℕ.* 2)

inc-2*-1ᵇ∷ : ∀ n → inc ⟦ n ℕ.* 2 ⇑⟧ ≡ 1ᵇ∷ ⟦ n ⇑⟧
inc-2*-1ᵇ∷ zero    i = 1ᵇ∷ []
inc-2*-1ᵇ∷ (suc n) i = inc (inc (inc-2*-1ᵇ∷ n i))

𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
𝔹-rightInv zero    = refl
𝔹-rightInv (suc x) = inc-suc ⟦ x ⇑⟧ ; cong suc (𝔹-rightInv x)

𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
𝔹-leftInv [] = refl
𝔹-leftInv (1ᵇ∷ x) = inc-2*-1ᵇ∷ ⟦ x ⇓⟧ ; cong 1ᵇ∷_ (𝔹-leftInv x)
𝔹-leftInv (2ᵇ∷ x) = cong inc (inc-2*-1ᵇ∷ ⟦ x ⇓⟧) ; cong 2ᵇ∷_ (𝔹-leftInv x)

𝔹⇔ℕ : 𝔹 ⇔ ℕ
𝔹⇔ℕ .fun = ⟦_⇓⟧
𝔹⇔ℕ .inv = ⟦_⇑⟧
𝔹⇔ℕ .rightInv = 𝔹-rightInv
𝔹⇔ℕ .leftInv  = 𝔹-leftInv
