{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Weighted.Semimodule {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Union rng
open import Control.Monad.Weighted.Cond rng

module _ {a} {A : Type a} where
  semimodule : LeftSemimodule rng (ℓ ℓ⊔ a)
  Monoid.𝑆 (CommutativeMonoid.monoid (LeftSemimodule.semimodule semimodule)) = W A
  Monoid._∙_ (CommutativeMonoid.monoid (LeftSemimodule.semimodule semimodule)) = _<|>_
  Monoid.ε (CommutativeMonoid.monoid (LeftSemimodule.semimodule semimodule)) = []
  Monoid.assoc (CommutativeMonoid.monoid (LeftSemimodule.semimodule semimodule)) xs ys zs = sym (<|>-assoc xs ys zs)
  Monoid.ε∙ (CommutativeMonoid.monoid (LeftSemimodule.semimodule semimodule)) _ = refl
  Monoid.∙ε (CommutativeMonoid.monoid (LeftSemimodule.semimodule semimodule)) xs = <|>-idr xs
  CommutativeMonoid.comm (LeftSemimodule.semimodule semimodule) = <|>-com
  LeftSemimodule._⋊_ semimodule = _⋊_
  LeftSemimodule.⟨*⟩⋊ semimodule = *-assoc-⋊
  LeftSemimodule.⟨+⟩⋊ semimodule x y xs = sym (⋊-distribʳ x y xs)
  LeftSemimodule.⋊⟨∪⟩ semimodule x y xs = sym (⋊-distribˡ x y xs)
  LeftSemimodule.1⋊ semimodule = 1⋊
  LeftSemimodule.0⋊ semimodule = 0⋊
