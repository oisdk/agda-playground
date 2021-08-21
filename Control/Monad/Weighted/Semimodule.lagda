\begin{code}
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
  semimodule .LeftSemimodule.semimodule .CommutativeMonoid.monoid .Monoid.𝑆 = Weighted A
  semimodule .LeftSemimodule.semimodule .CommutativeMonoid.monoid .Monoid._∙_ = _∪_
  semimodule .LeftSemimodule.semimodule .CommutativeMonoid.monoid .Monoid.ε = []
  semimodule .LeftSemimodule.semimodule .CommutativeMonoid.monoid .Monoid.assoc xs ys zs = sym (∪-assoc xs ys zs)
  semimodule .LeftSemimodule.semimodule .CommutativeMonoid.monoid .Monoid.ε∙ _ = refl
  semimodule .LeftSemimodule.semimodule .CommutativeMonoid.monoid .Monoid.∙ε xs = ∪-idr xs
  semimodule .LeftSemimodule.semimodule .CommutativeMonoid.comm = ∪-com
  semimodule .LeftSemimodule._⋊_ = _⋊_
  semimodule .LeftSemimodule.⟨*⟩⋊ = *-assoc-⋊
  semimodule .LeftSemimodule.⟨+⟩⋊ x y xs = sym (⋊-distribʳ x y xs)
  semimodule .LeftSemimodule.⋊⟨∪⟩ x y xs = sym (⋊-distribˡ x y xs)
  semimodule .LeftSemimodule.1⋊ = 1⋊
  semimodule .LeftSemimodule.0⋊ = 0⋊
  semimodule .LeftSemimodule.⋊∅ = ⋊∅
\end{code}
