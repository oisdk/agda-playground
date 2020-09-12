{-# OPTIONS --cubical --safe #-}

module Data.Lift where

open import Level

record Lift {a} ℓ (A : Type a) : Type (a ℓ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
