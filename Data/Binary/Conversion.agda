{-# OPTIONS --without-K --safe #-}

module Data.Binary.Conversion where

open import Data.Binary.Definition
open import Data.Binary.Increment
import Data.Nat as ℕ
open import Data.Nat using (ℕ; suc; zero)

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0ᵇ ⇓⟧ = 0
⟦ 1ᵇ xs ⇓⟧ = 1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2
⟦ 2ᵇ xs ⇓⟧ = 2 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2
