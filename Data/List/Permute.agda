{-# OPTIONS --cubical --safe #-}

module Data.List.Permute where

open import Prelude
open import Data.Nat
open import Data.List
open import Data.Nat.Properties using (_<ᴮ_)

infixr 6 _∹_
record Indexed {a} (A : Type a) : Type a where
  constructor _∹_
  field
    ind : ℕ
    val : A
open Indexed

mutual
  merge : List (Indexed A) → List (Indexed A) → List (Indexed A)
  merge = foldr mergeˡ id

  mergeˡ : Indexed A → (List (Indexed A) → List (Indexed A)) → List (Indexed A) → List (Indexed A)
  mergeˡ x xs [] = x ∷ xs []
  mergeˡ x xs (y ∷ ys) = merge⁺ x xs y ys (ind y <ᴮ ind x)

  merge⁺ : Indexed A → (List (Indexed A) → List (Indexed A)) → Indexed A → List (Indexed A) → Bool → List (Indexed A)
  merge⁺ x xs (j ∹ y) ys false = x ∷ xs ((j ∸ ind x) ∹ y ∷ ys)
  merge⁺ (i ∹ x) xs y ys true  = y ∷ mergeˡ (((i ∸ ind y) ∸ 1) ∹ x) xs ys

-- open import Algebra

-- merge-assoc : Associative (merge {A = A})
-- merge-assoc [] ys zs = {!!}
-- merge-assoc (x ∷ xs) [] zs = {!!}
-- merge-assoc (x ∷ xs) (y ∷ ys) [] = {!!}
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = {!!}
