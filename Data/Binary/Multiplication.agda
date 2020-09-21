{-# OPTIONS --cubical --safe #-}

module Data.Binary.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Addition

double : 𝔹 → 𝔹
double 0ᵇ = 0ᵇ
double (1ᵇ xs) = 2ᵇ double xs
double (2ᵇ xs) = 2ᵇ 1ᵇ xs

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
xs * 0ᵇ = 0ᵇ
xs * (1ᵇ ys) = go xs
  where
  ys₂ = double ys

  go : 𝔹 → 𝔹
  go 0ᵇ = 0ᵇ
  go (1ᵇ xs) = 1ᵇ (ys  + go xs)
  go (2ᵇ xs) = 2ᵇ (ys₂ + go xs)

xs * (2ᵇ ys) = go xs
  where
  go : 𝔹 → 𝔹
  go 0ᵇ = 0ᵇ
  go (1ᵇ xs) = 2ᵇ (   ys + go xs)
  go (2ᵇ xs) = 2ᵇ (1ᵇ ys + go xs)
