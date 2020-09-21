{-# OPTIONS --cubical --safe #-}

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

2^ : ℕ → ℕ
2^ zero = 1
2^ (suc n) = 2^ n * 2

go : 𝔹 → ℕ
go [] = zero
go (x ∷ xs) = suc (go xs * 2) * 2^ x

⟦_⇓⟧ : 𝔹 → ℕ
⟦ [] ⇓⟧ = zero
⟦ x  ∷ [] ⇓⟧ = 2^ x
⟦ x  ∷ zero   ∷ xs ⇓⟧ = suc (suc (go xs * 2)) * 2^ x
⟦ x₁ ∷ suc x₂ ∷ xs ⇓⟧ = go (x₁ ∷ x₂ ∷ xs)

fn : ℕ → _
fn n = ⟦ ⟦ n ⇑⟧ ⇓⟧
