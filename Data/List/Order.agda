{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary

module Data.List.Order {e r} {E : Type e} (totalOrder : TotalOrder E r) where

open import Data.List.Base
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

open TotalOrder totalOrder using (_≤_; _<_)

-- _≲_ : List E → List E → Type r
-- [] ≲ ys = Poly.⊤
-- (x ∷ xs) ≲ [] = Poly.⊥
-- (x ∷ xs) ≲ (y ∷ ys) = (x < y) ⊎ ((x ≤ y) × (xs ≲ ys))
