{-# OPTIONS --cubical --safe #-}

module Data.List.Kleene.Membership where

open import Prelude
open import Data.List.Kleene
open import Data.List.Kleene.Relation.Unary

infixr 5 _∈⋆_ _∈⁺_ _∉⋆_ _∉⁺_

_∈⋆_ _∉⋆_ : A → A ⋆ → Type _
x ∈⋆ xs = ◇⋆ (_≡ x) xs
x ∉⋆ xs = ¬ (x ∈⋆ xs)

_∈⁺_ _∉⁺_ : A → A ⁺ → Type _
x ∈⁺ xs = ◇⁺ (_≡ x) xs
x ∉⁺ xs = ¬ (x ∈⁺ xs)
