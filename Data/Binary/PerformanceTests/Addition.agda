{-# OPTIONS --cubical --safe #-}

module Data.Binary.PerformanceTests.Addition where

-- open import Prelude
-- open import Data.Binary.Definition
-- open import Data.Binary.Addition using (_+_)
-- open import Data.Binary.Multiplication using (_*_)
-- open import Data.Binary.Increment using (inc)

-- one-thousand : 𝔹
-- one-thousand = 2ᵇ 1ᵇ 1ᵇ 2ᵇ 1ᵇ 2ᵇ 2ᵇ 2ᵇ 2ᵇ 0ᵇ

-- pow-r : 𝔹 → ℕ → 𝔹
-- pow-r x zero    = 1ᵇ 0ᵇ
-- pow-r x (suc n) = x * pow-r (inc x) n

-- pow-l : 𝔹 → ℕ → 𝔹
-- pow-l x zero    = 1ᵇ 0ᵇ
-- pow-l x (suc n) = pow-l (inc x) n * x

-- n : ℕ
-- n = 6

-- f : 𝔹
-- f = one-thousand

-- _ : pow-r f n ≡ pow-l f n
-- _ = refl
