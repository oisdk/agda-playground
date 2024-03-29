{-# OPTIONS --cubical --safe #-}

module Data.List.Syntax where

open import Data.List
open import Prelude

open import Data.Vec.Sigma using () renaming (toList to [_]) public
open import Data.Vec.Sigma

[_][_] : ∀ n → Vec A n → List A
[ n ][ xs ] = toList {n = n} xs

-- record ListSyntax {a b} (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
--   field [_] : B → List A

-- open ListSyntax ⦃ ... ⦄ public

-- instance
--   cons : ⦃ _ : ListSyntax A B ⦄ →  ListSyntax A (A × B)
--   [_] ⦃ cons ⦄ (x , xs) = x ∷ [ xs ]

-- instance
--   sing : ListSyntax A A
--   [_] ⦃ sing ⦄ = _∷ []

