{-# OPTIONS --cubical --safe #-}

module Data.Binary.Testers where

open import Prelude
open import Data.Binary.Conversion
open import Data.Binary.Definition
open import Data.List using (List; _⋯_)
open import Data.List.Sugar using (liftA2)

test : (𝔹 → 𝔹 → 𝔹) →
       (ℕ → ℕ → ℕ) →
       ℕ → Type₀
test bf nf n =
  liftA2 (λ n m → bf ⟦ n ⇑⟧ ⟦ m ⇑⟧) (0 ⋯ n) (0 ⋯ n) ≡
  liftA2 (λ n m → ⟦ nf n m ⇑⟧) (0 ⋯ n) (0 ⋯ n)

import Data.Nat as ℕ
open import Data.Binary.Addition using (_+_)
open import Data.Binary.Multiplication using (_*_)
open import Data.Binary.Subtraction using (_-_)

_ : test _+_ ℕ._+_ 15
_ = refl

_ : test _*_ ℕ._*_ 15
_ = refl

_ : test _-_ ℕ._∸_ 15
_ = refl
