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
  semimodule : Semimodule rng (ℓ ℓ⊔ a)
  Monoid.𝑆 (CommutativeMonoid.monoid (Semimodule.semimodule semimodule)) = Weighted A
  Monoid._∙_ (CommutativeMonoid.monoid (Semimodule.semimodule semimodule)) = _∪_
  Monoid.ε (CommutativeMonoid.monoid (Semimodule.semimodule semimodule)) = []
  Monoid.assoc (CommutativeMonoid.monoid (Semimodule.semimodule semimodule)) xs ys zs = sym (∪-assoc xs ys zs)
  Monoid.ε∙ (CommutativeMonoid.monoid (Semimodule.semimodule semimodule)) _ = refl
  Monoid.∙ε (CommutativeMonoid.monoid (Semimodule.semimodule semimodule)) xs = ∪-idr xs
  CommutativeMonoid.comm (Semimodule.semimodule semimodule) = ∪-com
  Semimodule._⋊_ semimodule = _⋊_
  Semimodule.⟨∗⟩⋊ semimodule = ∗-assoc-⋊
  Semimodule.⟨+⟩⋊ semimodule x y xs = sym (⋊-distribʳ x y xs)
  Semimodule.⋊⟨∪⟩ semimodule x y xs = sym (⋊-distribˡ x y xs)
  Semimodule.1⋊ semimodule = 1⋊
  Semimodule.0⋊ semimodule = 0⋊
  Semimodule.⋊∅ semimodule = ⋊∅
\end{code}
