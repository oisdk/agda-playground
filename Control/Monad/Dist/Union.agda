{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Dist.Union {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels
open import Control.Monad.Dist.Definition rng
open import Control.Monad.Dist.Eliminators rng


union-alg : W A → Recursor A (W A)
[ union-alg ys ]-set = trunc
[ union-alg ys ] p & x ∷ _ ⟨ pxs ⟩ = p & x ∷ pxs
[ union-alg ys ][] = ys
[ union-alg ys ]-dup p q x _ pxs = dup p q x pxs
[ union-alg ys ]-com p x q y _ pxs = com p x q y pxs
[ union-alg ys ]-del x _ pxs = del x pxs

_∪_ : W A → W A → W A
xs ∪ ys = union-alg ys ↓ xs

∪-assoc : (xs ys zs : W A) → xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs
∪-assoc xs ys zs = ∪-assoc′ ys zs ⇓≡ xs
  where
  ∪-assoc′ : ∀ ys zs → EqualityProof A (λ xs → xs ∪ (ys ∪ zs) ⊜ (xs ∪ ys) ∪ zs)
  ⟦ ∪-assoc′ ys zs ⟧≡[] = refl
  ⟦ ∪-assoc′ ys zs ⟧≡ p & x ∷ xs ⟨ P ⟩ = cong (p & x ∷_) P
