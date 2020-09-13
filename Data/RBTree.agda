{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Data.RBTree {e} {E : Type e} {r} (totalOrder : TotalOrder E r) where

open import Relation.Binary.Construct.Bounded totalOrder

open TotalOrder totalOrder using (_≤?_)

data Colour : Type₀ where
  red black : Colour

data Tree (lb ub : [∙]) : Type (e ℓ⊔ r) where
  leaf : lb [≤] ub → Tree lb ub
  node : (x : E) → Tree lb [ x ] → Tree [ x ] ub → Tree lb ub

private
  variable
    lb ub : [∙]

insertWithin : (x : E) → (lb [≤] [ x ]) → ([ x ] [≤] ub) → Tree lb ub → Tree lb ub
insertWithin x lb≤x x≤ub (leaf p) = node x (leaf lb≤x) (leaf x≤ub)
insertWithin x lb≤x x≤ub (node y ls rs) with x ≤? y
insertWithin x lb≤x x≤ub (node y ls rs) | inl x≤y = node y (insertWithin x lb≤x x≤y ls) rs
insertWithin x lb≤x x≤ub (node y ls rs) | inr y≤x = node y ls (insertWithin x y≤x x≤ub rs)
