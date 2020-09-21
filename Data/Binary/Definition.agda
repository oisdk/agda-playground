{-# OPTIONS --without-K --safe #-}

module Data.Binary.Definition where

open import Level

infixr 5 1ᵇ_ 2ᵇ_
data 𝔹 : Type₀ where
  0ᵇ : 𝔹
  1ᵇ_ : 𝔹 → 𝔹
  2ᵇ_ : 𝔹 → 𝔹
