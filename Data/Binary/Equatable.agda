{-# OPTIONS --cubical --safe #-}

module Data.Binary.Equatable where

open import Prelude
open import Data.Binary.Definition

infix 4 _≡ᴮ_
_≡ᴮ_ : 𝔹 → 𝔹 → Bool
0ᵇ      ≡ᴮ 0ᵇ       = true
(1ᵇ xs) ≡ᴮ (1ᵇ ys) = xs ≡ᴮ ys
(2ᵇ xs) ≡ᴮ (2ᵇ ys) = xs ≡ᴮ ys
_       ≡ᴮ _        = false

open import Relation.Nullary.Discrete.FromBoolean

_≟_ : Discrete 𝔹
_≟_ = from-bool-eq _≡ᴮ_ ≡ᴮ⇒≡ T-refl
  where
  ≡ᴮ⇒≡ : ∀ xs ys → T (xs ≡ᴮ ys) → xs ≡ ys
  ≡ᴮ⇒≡ 0ᵇ      0ᵇ      xs≡ys i = 0ᵇ
  ≡ᴮ⇒≡ (1ᵇ xs) (1ᵇ ys) xs≡ys i = 1ᵇ ≡ᴮ⇒≡ xs ys xs≡ys i
  ≡ᴮ⇒≡ (2ᵇ xs) (2ᵇ ys) xs≡ys i = 2ᵇ ≡ᴮ⇒≡ xs ys xs≡ys i

  T-refl : ∀ xs → T (xs ≡ᴮ xs)
  T-refl 0ᵇ = tt
  T-refl (1ᵇ xs) = T-refl xs
  T-refl (2ᵇ xs) = T-refl xs
