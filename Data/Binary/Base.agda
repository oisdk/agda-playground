{-# OPTIONS --cubical --safe #-}

module Data.Binary.Base where

open import Prelude

double : 𝔹 → 𝔹
double [] = []
double (1ᵇ∷ xs) = 2ᵇ∷ double xs
double (2ᵇ∷ xs) = 2ᵇ∷ 1ᵇ∷ xs


_≡ᵇ_ : 𝔹 → 𝔹 → Bool
[] ≡ᵇ [] = true
[] ≡ᵇ (1ᵇ∷ ys) = false
[] ≡ᵇ (2ᵇ∷ ys) = false
(1ᵇ∷ xs) ≡ᵇ [] = false
(1ᵇ∷ xs) ≡ᵇ (1ᵇ∷ ys) = xs ≡ᵇ ys
(1ᵇ∷ xs) ≡ᵇ (2ᵇ∷ ys) = false
(2ᵇ∷ xs) ≡ᵇ [] = false
(2ᵇ∷ xs) ≡ᵇ (1ᵇ∷ ys) = false
(2ᵇ∷ xs) ≡ᵇ (2ᵇ∷ ys) = xs ≡ᵇ ys

-- testers : ℕ → Type₀
-- testers n = bins n n ≡ nats n n
--   where
--   open import Data.List
--   open import Data.List.Syntax
--   open import Data.List.Sugar
--   import Agda.Builtin.Nat as Nat

--   upTo : (ℕ → A) → ℕ → List A
--   upTo f zero = []
--   upTo f (suc n) = f zero List.∷ upTo (f ∘ suc) n

--   bins : ℕ → ℕ → List 𝔹
--   bins ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure (⟦ n ⇑⟧ - ⟦ m ⇑⟧)

--   nats : ℕ → ℕ → List 𝔹
--   nats ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure ⟦ n Nat.- m ⇑⟧

-- _ : testers 100
-- _ = refl
