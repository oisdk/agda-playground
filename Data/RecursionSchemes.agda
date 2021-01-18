{-# OPTIONS --cubical --safe #-}

module Data.RecursionSchemes where

open import Prelude
open import Data.Functor

record Recursive ℓ₁ : Type (ℓsuc ℓ₁) where
  field
    R  : Type ℓ₁
    functor : Functor ℓ₁ ℓ₁
  open Functor functor public
  field
    cata : (F A → A) → R → A

