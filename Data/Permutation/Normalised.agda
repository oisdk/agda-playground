{-# OPTIONS --safe #-}

module Data.Permutation.Normalised where

open import Data.Permutation.Normalised.Definition
  using ( Diffs
        ; _⊙_
        ; supp
        ; disp-diffs
        ; disp-swaps
        )
  public
open import Data.Permutation.Normalised.Unnorm
  using ( [_]↑
        ; ⊙↑-hom
        )
  public
open import Data.Permutation.Normalised.Norm
  using ( [_]↓
        ; ⊙↓-hom
        )
  public
open import Data.Permutation.Normalised.Injective
  using ( ⊙-inj
        ; inj-⊙
        )
  public
open import Data.Permutation.Normalised.RoundTrip
  using ( norm-inv
        )
  public
open import Data.Permutation.Normalised.Group
  using ( _⊕_
        ; diffs-comp
        ; ⊕-hom
        ; ⊕-assoc
        ; negate
        ; neg-inv-d
        )
  public
