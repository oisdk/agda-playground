{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Prelude
open import Relation.Binary

module Data.AVLTree.Mapping {k} {K : Type k} {r₁ r₂} (totalOrder : TotalOrder K r₁ r₂) where

open import Relation.Binary.Construct.Bounded totalOrder
open import Data.Nat using (_+_)
open TotalOrder totalOrder using (_<?_; compare)
open TotalOrder b-ord using (<-trans) renaming (refl to <-refl)
import Data.Empty.UniversePolymorphic as Poly

open import Data.AVLTree.Internal totalOrder

private
  variable
    n m : ℕ
    v : Level
    Val : K → Type v

data Mapping (Val : K → Type v) : Type (k ℓ⊔ v ℓ⊔ r₁) where
  [_] : Tree Val [⊥] [⊤] n → Mapping Val
  quot : (xs : Tree Val [⊥] [⊤] n) (ys : Tree Val [⊥] [⊤] m) → toList xs ≡ toList ys → [ xs ] ≡ [ ys ]
  trunc : isSet (Mapping Val)

lookup′ : (x : K) → Mapping Val → Maybe (Val x)
lookup′ x [ xs ] = lookup x xs
lookup′ x (quot xs ys p j) = {!!}
lookup′ x (trunc xs xs₁ x₁ y i i₁) = {!!}
