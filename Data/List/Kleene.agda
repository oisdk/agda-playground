{-# OPTIONS --safe --cubical #-}

module Data.List.Kleene where

open import Prelude
open import Data.Fin

mutual
  infixr 5 _&_ ∹_
  infixl 5 _⁺ _⋆

  record _⁺ (A : Type a) : Type a where
    inductive
    constructor _&_
    field
      head : A
      tail : A ⋆

  data _⋆ (A : Type a) : Type a where
    [] : A ⋆
    ∹_ : A ⁺ → A ⋆

open _⁺ public

mutual
  foldr⁺ : (A → B → B) → B → A ⁺ → B
  foldr⁺ f b (x & xs) = f x (foldr⋆ f b xs)

  foldr⋆ : (A → B → B) → B → A ⋆ → B
  foldr⋆ f b [] = b
  foldr⋆ f b (∹ xs) = foldr⁺ f b xs

length⋆ : A ⋆ → ℕ
length⋆ = foldr⋆ (const suc) zero

length⁺ : A ⁺ → ℕ
length⁺ = foldr⁺ (const suc) zero

mutual
  _!⁺_ : (xs : A ⁺) → Fin (length⁺ xs) → A
  xs !⁺ f0  = xs .head
  xs !⁺ fs i = xs .tail !⋆ i

  _!⋆_ : (xs : A ⋆) → Fin (length⋆ xs) → A
  (∹ xs) !⋆ i = xs !⁺ i

map⋆ : (A → B) → A ⋆ → B ⋆
map⋆ f = foldr⋆ (λ x xs → ∹ f x & xs) []

map⁺ : (A → B) → A ⁺ → B ⁺
map⁺ f (x & xs) = f x & map⋆ f xs

mutual
  _⋆++⋆_ : A ⋆ → A ⋆ → A ⋆
  [] ⋆++⋆ ys = ys
  (∹ xs) ⋆++⋆ ys = ∹ (xs ⁺++⋆ ys)

  _⁺++⋆_ : A ⁺ → A ⋆ → A ⁺
  head (xs ⁺++⋆ ys) = head xs
  tail (xs ⁺++⋆ ys) = tail xs ⋆++⋆ ys
