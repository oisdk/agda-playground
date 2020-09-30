{-# OPTIONS --without-K --safe #-}

module Data.Binary.Definition where

open import Level
open import Data.Bits public renaming (Bits to 𝔹; [] to 0ᵇ; 0∷_ to 1ᵇ_; 1∷_ to 2ᵇ∷_)

-- The following causes a performance hit:

-- open import Agda.Builtin.List using ([]; _∷_; List)
-- open import Agda.Builtin.Bool using (Bool; true; false)

-- 𝔹 : Type₀
-- 𝔹 = List Bool

-- infixr 8 1ᵇ_ 2ᵇ_
-- pattern 0ᵇ = []
-- pattern 1ᵇ_ xs = false ∷ xs
-- pattern 2ᵇ_ xs = true  ∷ xs
