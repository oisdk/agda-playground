{-# OPTIONS --safe #-}

open import Prelude hiding (_↔_)

module Data.Permutation.NonNorm {A : Type a} (_≟_ : Discrete A) where

open import Data.Permutation.Swap _≟_

open import Data.List hiding ([]; _∷_)
import Data.List as ConsR

Swaps : Type a
Swaps = List (A × A)

infixl 5 _∘⟨_⟩
pattern _∘⟨_⟩ xs x = x ConsR.∷ xs

pattern ⟨⟩ = ConsR.[]

infixr 4.5 _·_
_·_ : Swaps → A → A
_·_ = flip (foldl (flip (uncurry _↔_·_)))
