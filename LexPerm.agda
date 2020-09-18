{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary

module LexPerm {e r} {E : Type e} (totalOrder : TotalOrder E r) where

open import Data.List
