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

-- infixl 4 _⊕_
-- _⊕_ : (ℕ → Type p) → ℕ → ℕ → Type p
-- _⊕_ P n m = P (n + m)

-- data Spine⁺ {p} (P : ℕ → Type p) : 𝔹 → Type p where
--   nil : Spine⁺ P []
--   conss : ∀ n → P n → Spine⁺ (P ⊕ n ⊕ 1) ns → Spine⁺ P (n ∷ ns)

-- data Spine {p} (P : ℕ → Type p) : 𝔹 → Type p where
--   nil : Spine P []
--   conss : ∀ n → P n → Spine⁺ (P ⊕ n) ns → Spine P (n ∷ ns)

-- cons : (∀ {m} → P m → P m → P (suc m)) → P zero → Spine P ns → Spine P (inc ns)
-- cons _*_ x nil = conss zero x nil
-- cons _*_ x (conss n x₁ nil) = conss zero x (conss n x₁ nil)
-- cons _*_ x (conss n x₁ (conss zero x₂ x₃)) = {!conss (suc n) {!!} x₃!}
-- cons _*_ x (conss n x₁ (conss (suc n₁) x₂ x₃)) = conss zero {!!} (conss n {!!} (cons n₁ {!!} x₃))
