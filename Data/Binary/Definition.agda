{-# OPTIONS --without-K --safe #-}

module Data.Binary.Definition where

open import Level

infixr 5 1ᵇ∷_ 2ᵇ∷_
data 𝔹 : Type₀ where
  [] : 𝔹
  1ᵇ∷_ : 𝔹 → 𝔹
  2ᵇ∷_ : 𝔹 → 𝔹
