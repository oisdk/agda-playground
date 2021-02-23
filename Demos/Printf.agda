{-# OPTIONS --cubical #-}

module Demos.Printf where

open import Data.List
open import Data.String
open import Prelude
open import Data.Nat.Show

data Fstr : Type₀ where
  [] : Fstr
  %s_ : Fstr → Fstr
  %i_ : Fstr → Fstr
  _∷_ : Char → Fstr → Fstr

parse : String → Fstr
parse = go ∘ unpack
  where
  go : List Char → Fstr
  go ('%' ∷ 's' ∷ xs) = %s go xs
  go ('%' ∷ 'i' ∷ xs) = %i go xs
  go [] = []
  go (x ∷ xs) = x ∷ go xs

Format : Fstr → Type₀
Format [] = String
Format (%s xs) = String → Format xs
Format (%i xs) = ℕ → Format xs
Format (x ∷ xs) = Format xs

format : (xs : Fstr) → Format xs
format = go pack
  where
  go : (List Char → String) → (xs : Fstr) → Format xs
  go k [] = k []
  go k (%s xs) s = go (k ∘ (unpack s ++_)) xs
  go k (%i xs) i = go (k ∘ (unpack (showℕ i) ++_)) xs
  go k (x ∷ xs)  = go (k ∘ (x ∷_)) xs

printf : (fstr : String) → Format (parse fstr)
printf fstr = format (parse fstr)
