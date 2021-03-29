{-# OPTIONS --cubical --safe #-}

module Data.Finite where

open import Prelude
open import Data.Fin

𝒞 : Type a → Type a
𝒞 A = ∃[ n ] ∥ A ≃ Fin n ∥

ℂ : Type _
ℂ = Σ[ T ⦂ Type₀ ] 𝒞 T
