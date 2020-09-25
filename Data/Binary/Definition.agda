{-# OPTIONS --without-K --safe #-}

module Data.Binary.Definition where

open import Level


data 𝔹 : Type₀ where
  0ᵇ : 𝔹
  1ᵇ_ : 𝔹 → 𝔹
  2ᵇ_ : 𝔹 → 𝔹

-- The following causes a performance hit:

-- open import Agda.Builtin.List using ([]; _∷_; List)
-- open import Agda.Builtin.Bool using (Bool; true; false)

-- 𝔹 : Type₀
-- 𝔹 = List Bool

-- infixr 8 1ᵇ_ 2ᵇ_
-- pattern 0ᵇ = []
-- pattern 1ᵇ_ xs = false ∷ xs
-- pattern 2ᵇ_ xs = true  ∷ xs
