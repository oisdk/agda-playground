{-# OPTIONS --cubical --safe #-}

module Data.Binary.Conversion.Strict where

open import Data.Binary.Definition
open import Data.Binary.Increment.Strict
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Fold
open import Strict
open import Data.Nat.DivMod
open import Data.Bool

⟦_⇑⟧′ : ℕ → 𝔹
⟦_⇑⟧′ = foldl-ℕ inc′ 0ᵇ

⟦_⇓⟧′ : 𝔹 → ℕ
⟦ 0ᵇ ⇓⟧′ = zero
⟦ 1ᵇ xs ⇓⟧′ = let! xs′ =! ⟦ xs ⇓⟧′ in! 1 ℕ.+ xs′ ℕ.* 2
⟦ 2ᵇ xs ⇓⟧′ = let! xs′ =! ⟦ xs ⇓⟧′ in! 2 ℕ.+ xs′ ℕ.* 2
