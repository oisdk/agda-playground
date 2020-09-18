{-# OPTIONS --without-K --safe #-}

module Data.Binary.Increment where

open import Data.Binary.Definition

inc : 𝔹 → 𝔹
inc [] = 1ᵇ∷ []
inc (1ᵇ∷ xs) = 2ᵇ∷ xs
inc (2ᵇ∷ xs) = 1ᵇ∷ inc xs
