{-# OPTIONS --cubical --safe #-}

module Data.Bool.Truth where

open import Data.Empty
open import Data.Unit
open import Level
open import Data.Bool.Base

T : Bool → Type₀
T true  = ⊤
T false = ⊥
