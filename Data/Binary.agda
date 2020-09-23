{-# OPTIONS --cubical --safe #-}

module Data.Binary where

open import Data.Binary.Definition public
  using (𝔹; 0ᵇ; 1ᵇ_; 2ᵇ_)
open import Data.Binary.Conversion public
  using (⟦_⇑⟧; ⟦_⇓⟧)
open import Data.Binary.Addition public
  using (_+_)
open import Data.Binary.Multiplication public
  using (_*_)
open import Data.Binary.Subtraction public
  using (_-_)
open import Data.Binary.Isomorphism public
  using (𝔹⇔ℕ)
open import Data.Binary.Increment public
  using (inc)
