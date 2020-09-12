{-# OPTIONS --cubical --safe #-}

-- Free join semilattice
module Algebra.Construct.Free.Semilattice where

open import Algebra.Construct.Free.Semilattice.Definition public
open import Algebra.Construct.Free.Semilattice.Eliminators public
open import Algebra.Construct.Free.Semilattice.Union public using (_∪_; 𝒦-semilattice)
open import Algebra.Construct.Free.Semilattice.Homomorphism public using (μ; ∙-hom)
