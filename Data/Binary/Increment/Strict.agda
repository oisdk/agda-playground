{-# OPTIONS --cubical --safe #-}

module Data.Binary.Increment.Strict where

open import Prelude
open import Strict
open import Data.Binary.Definition
open import Data.Bits.Strict
open import Data.Binary.Increment

inc′ : 𝔹 → 𝔹
inc′ 0ᵇ      = 1ᵇ 0ᵇ
inc′ (1ᵇ xs) = 2ᵇ xs
inc′ (2ᵇ xs) = 0∷! inc′ xs

inc′≡inc : ∀ xs → inc′ xs ≡ inc xs
inc′≡inc 0ᵇ = refl
inc′≡inc (1ᵇ xs) = refl
inc′≡inc (2ᵇ xs) = 0∷!≡0∷ (inc′ xs) ; cong 1ᵇ_ (inc′≡inc xs)
