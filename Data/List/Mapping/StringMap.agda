{-# OPTIONS --cubical --safe #-}

module Data.List.Mapping.StringMap where

open import Data.String using (String; stringOrd)
open import Data.List.Mapping stringOrd
open import Prelude
open import Data.Maybe


Row : Type₁
Row = name ↦ Type₀

Record : Row → Type₀
Record sig = name ↦ sig [ name ] |? ⊥

example : Record ("age" ≔ ℕ , "name" ≔ String , ∅)
example = "age" ≔ 30
        , ∅
