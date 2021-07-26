{-# OPTIONS --cubical --guarded #-}

module Codata.CoNat where

open import Prelude
open import LaterPrims

data ℕω : Type where
  zero : ℕω
  suc  : ▹ ℕω → ℕω

ω : ℕω
ω = fix suc
