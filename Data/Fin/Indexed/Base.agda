{-# OPTIONS --without-K --safe #-}

module Data.Fin.Indexed.Base where

open import Data.Nat using (ℕ; suc; zero)
open import Level

private variable n m : ℕ

-- This is the more traditional definition of Fin,
-- that you would usually find in Agda code.
-- I tend to use the other one because cubical
-- Agda doesn't yet support transport along
-- equalities of indexed types.
data Fin : ℕ → Type₀ where
  f0 : Fin (suc n)
  fs : Fin n → Fin (suc n)
