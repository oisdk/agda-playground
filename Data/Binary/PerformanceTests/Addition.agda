{-# OPTIONS --cubical --safe #-}

module Data.Binary.PerformanceTests.Addition where

open import Prelude
open import Data.Binary.Definition
open import Data.Binary.Addition using (_+_)

sum-r : 𝔹 → ℕ → 𝔹
sum-r′ : 𝔹 → ℕ → 𝔹

sum-r′ x zero    = x
sum-r′ x (suc n) = x + sum-r (2ᵇ x) n

sum-r x zero    = x
sum-r x (suc n) = x + sum-r′ (1ᵇ x) n

sum-l : 𝔹 → ℕ → 𝔹
sum-l′ : 𝔹 → ℕ → 𝔹

sum-l′ x zero    = x
sum-l′ x (suc n) = sum-l (2ᵇ x) n + x

sum-l x zero    = x
sum-l x (suc n) = sum-l′ (1ᵇ x) n + x

one-thousand : 𝔹
one-thousand = 2ᵇ 1ᵇ 1ᵇ 2ᵇ 1ᵇ 2ᵇ 2ᵇ 2ᵇ 2ᵇ 0ᵇ

f : 𝔹
f = one-thousand

n : ℕ
n = 1000

-- The actual performance test (uncomment and time how long it takes to type-check)
-- _ : sum-l one-thousand n ≡ sum-r one-thousand n
-- _ = refl
