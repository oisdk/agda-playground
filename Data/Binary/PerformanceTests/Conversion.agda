{-# OPTIONS --cubical #-}

module Data.Binary.PerformanceTests.Conversion where

open import Prelude
open import Data.Binary.Definition
open import Data.Binary.Conversion using (⟦_⇓⟧)
-- open import Data.Binary.Conversion.Strict
open import Data.Binary.Conversion.Fast

-- one-thousand : 𝔹
-- one-thousand = 2ᵇ 1ᵇ 1ᵇ 2ᵇ 1ᵇ 2ᵇ 2ᵇ 2ᵇ 2ᵇ 0ᵇ

-- f : 𝔹
-- f = one-thousand

n : ℕ
n = 5000000

-- The actual performance test (uncomment and time how long it takes to type-check)
_ : ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
_ = refl
