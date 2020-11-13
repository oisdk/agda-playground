{-# OPTIONS --cubical --safe #-}

module Karatsuba where

open import Prelude

data Tree {a} (A : Type a) : Type a where


record Builder {a} (A : Type a) : Type a where
  field
    shift : ℕ
