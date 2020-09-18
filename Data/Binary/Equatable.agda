{-# OPTIONS --cubical --safe #-}

module Data.Binary.Equatable where

open import Prelude
open import Data.Binary.Definition

infix 4 _≡ᴮ_
_≡ᴮ_ : 𝔹 → 𝔹 → Bool
[]       ≡ᴮ []       = true
[]       ≡ᴮ (1ᵇ∷ ys) = false
[]       ≡ᴮ (2ᵇ∷ ys) = false
(1ᵇ∷ xs) ≡ᴮ []       = false
(1ᵇ∷ xs) ≡ᴮ (1ᵇ∷ ys) = xs ≡ᴮ ys
(1ᵇ∷ xs) ≡ᴮ (2ᵇ∷ ys) = false
(2ᵇ∷ xs) ≡ᴮ []       = false
(2ᵇ∷ xs) ≡ᴮ (1ᵇ∷ ys) = false
(2ᵇ∷ xs) ≡ᴮ (2ᵇ∷ ys) = xs ≡ᴮ ys

≡ᴮ⇒≡ : ∀ xs ys → T (xs ≡ᴮ ys) → xs ≡ ys
≡ᴮ⇒≡ []       []       xs≡ys i = []
≡ᴮ⇒≡ (1ᵇ∷ xs) (1ᵇ∷ ys) xs≡ys i = 1ᵇ∷ ≡ᴮ⇒≡ xs ys xs≡ys i
≡ᴮ⇒≡ (2ᵇ∷ xs) (2ᵇ∷ ys) xs≡ys i = 2ᵇ∷ ≡ᴮ⇒≡ xs ys xs≡ys i

≡⇒≡ᴮ : ∀ xs ys → xs ≡ ys → T (xs ≡ᴮ ys)
≡⇒≡ᴮ xs ys p = subst (λ z → T (xs ≡ᴮ z)) p (go xs)
  where
  go : ∀ xs → T (xs ≡ᴮ xs)
  go [] = tt
  go (1ᵇ∷ xs) = go xs
  go (2ᵇ∷ xs) = go xs

_≟_ : Discrete 𝔹
xs ≟ ys = ⟦yes ≡ᴮ⇒≡ xs ys ,no ≡⇒≡ᴮ xs ys ⟧ (from-bool (xs ≡ᴮ ys))

