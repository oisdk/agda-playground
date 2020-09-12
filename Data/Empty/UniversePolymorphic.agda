{-# OPTIONS --cubical --safe #-}

module Data.Empty.UniversePolymorphic where

open import Prelude hiding (⊥)
import Data.Empty as Monomorphic

data ⊥ {ℓ} : Type ℓ where

Poly⊥⇔Mono⊥ : ∀ {ℓ} → ⊥ {ℓ} ⇔ Monomorphic.⊥
Poly⊥⇔Mono⊥ .fun      ()
Poly⊥⇔Mono⊥ .inv      ()
Poly⊥⇔Mono⊥ .leftInv  ()
Poly⊥⇔Mono⊥ .rightInv ()
