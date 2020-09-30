{-# OPTIONS --without-K --safe #-}

module Data.Bits where

open import Level

infixr 8 0∷_ 1∷_
data Bits : Type₀ where
  [] : Bits
  0∷_ : Bits → Bits
  1∷_ : Bits → Bits


