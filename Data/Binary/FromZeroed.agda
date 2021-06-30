{-# OPTIONS --cubical --safe #-}

module Data.Binary.FromZeroed where

open import Data.Binary.Definition
open import Prelude

inc-z : 𝔹 → 𝔹
inc-z 0ᵇ = 2ᵇ 0ᵇ
inc-z (1ᵇ xs) = 2ᵇ xs
inc-z (2ᵇ xs) = 1ᵇ inc-z xs

toZ : 𝔹 → 𝔹
toZ 0ᵇ = 0ᵇ
toZ (1ᵇ xs) = 2ᵇ toZ xs
toZ (2ᵇ xs) = 1ᵇ inc-z (toZ xs)

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = 1ᵇ ones n xs

fromZ₁ : ℕ → 𝔹 → 𝔹
fromZ₁ n 0ᵇ      = 0ᵇ
fromZ₁ n (1ᵇ xs) = fromZ₁ (suc n) xs
fromZ₁ n (2ᵇ xs) = 2ᵇ ones n (fromZ₁ 0 xs)

fromZ : 𝔹 → 𝔹
fromZ 0ᵇ = 0ᵇ
fromZ (1ᵇ xs) = fromZ₁ zero xs
fromZ (2ᵇ xs) = 1ᵇ fromZ xs

import Data.Binary.Conversion.Fast as Fast

open import Data.List using (List; _⋯_; map)

round-trip : ℕ → Type
round-trip n = map (fromZ ∘ toZ) nums ≡ nums
  where
  nums : List 𝔹
  nums = map Fast.⟦_⇑⟧ (0 ⋯ n)

_ : round-trip 300
_ = refl
