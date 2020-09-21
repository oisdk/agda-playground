{-# OPTIONS --cubical --safe #-}

module Data.Binary.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Addition

double : 𝔹 → 𝔹
double 0ᵇ = 0ᵇ
double (1ᵇ xs) = 2ᵇ double xs
double (2ᵇ xs) = 2ᵇ 1ᵇ xs

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
xs * 0ᵇ = 0ᵇ
xs * (1ᵇ ys) = go xs
  where
  ys2 = double ys

  go : 𝔹 → 𝔹
  go 0ᵇ = 0ᵇ
  go (1ᵇ xs) = 1ᵇ ys + go xs
  go (2ᵇ xs) = 2ᵇ (ys2 + go xs)

xs * (2ᵇ ys) = go xs
  where
  go : 𝔹 → 𝔹
  go 0ᵇ = 0ᵇ
  go (1ᵇ xs) = 2ᵇ ys + go xs
  go (2ᵇ xs) = 2ᵇ (1ᵇ ys) + go xs

-- open import Prelude
-- open import Data.Binary.Conversion

-- testers : ℕ → Type₀
-- testers n = bins n n ≡ nats n n
--   where
--   open import Data.List
--   open import Data.List.Syntax
--   open import Data.List.Sugar
--   import Agda.Builtin.Nat as Nat

--   upTo : (ℕ → A) → ℕ → List A
--   upTo f zero = 0ᵇ
--   upTo f (suc n) = f zero List.∷ upTo (f ∘ suc) n

--   bins : ℕ → ℕ → List 𝔹
--   bins ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure (⟦ n ⇑⟧ * ⟦ m ⇑⟧)

--   nats : ℕ → ℕ → List 𝔹
--   nats ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure ⟦ n Nat.* m ⇑⟧

-- _ : testers 10
-- _ = refl
