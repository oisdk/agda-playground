{-# OPTIONS --cubical --safe #-}

module Data.Array.Skew where

open import Prelude
open import Data.Binary.Skew
open import Data.List
open import Data.Nat using (_+_)

private
  variable
    p : Level
    P : ℕ → Type p
    n : ℕ
    ns : 𝔹

infixl 6 _∔_
_∔_ : ℕ → ℕ → ℕ
zero  ∔ m = m
suc n ∔ m = n ∔ suc m

infixl 4 _⊕_
_⊕_ : (ℕ → Type p) → ℕ → ℕ → Type p
_⊕_ P n m = P (n ∔ m)

data Spine⁺ {p} (P : ℕ → Type p) : 𝔹 → Type p where
  nil : Spine⁺ P []
  conss : ∀ n → P n → Spine⁺ (P ⊕ suc n) ns → Spine⁺ P (n ∷ ns)

data Spine {p} (P : ℕ → Type p) : 𝔹 → Type p where
  nil : Spine P []
  conss : ∀ n → P n → Spine⁺ (P ⊕ n) ns → Spine P (n ∷ ns)

-- cons : (∀ {m} → P m → P m → P (suc m)) → P zero → Spine P ns → Spine P (inc ns)
-- cons _*_ x nil = conss zero x nil
-- cons _*_ x (conss n x₁ nil) = conss zero x (conss n x₁ nil)
-- cons _*_ x (conss n x₁ (conss zero x₂ xs)) = conss (suc n) (x₁ * x₁) xs
-- cons _*_ x (conss n x₁ (conss (suc m) x₂ xs)) = conss zero x (conss n x₁ (conss m x₂ {!!}))
