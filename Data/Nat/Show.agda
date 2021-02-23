{-# OPTIONS --cubical --safe #-}

module Data.Nat.Show where

open import Prelude
open import Data.Nat
open import Data.Nat.DivMod
open import Data.String
open import Data.List

showDig : ℕ → Char
showDig 0 = '0'
showDig 1 = '1'
showDig 2 = '2'
showDig 3 = '3'
showDig 4 = '4'
showDig 5 = '5'
showDig 6 = '6'
showDig 7 = '7'
showDig 8 = '8'
showDig 9 = '9'
showDig _ = '!'

showsℕ : ℕ → List Char → List Char
showsℕ n xs = go xs n n
  where
  go : List Char → ℕ → ℕ → List Char
  go a zero      _       = a
  go a n@(suc _) (suc t) = go (showDig (rem n 10) ∷ a) (n ÷ 10) t
  go a (suc _)   zero    = a

showℕ : ℕ → String
showℕ n = pack (showsℕ n [])
