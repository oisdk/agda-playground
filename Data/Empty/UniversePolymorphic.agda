{-# OPTIONS --cubical --safe #-}

open import Prelude hiding (⊥)

module Data.Empty.UniversePolymorphic {ℓ : Level} where

import Data.Empty as Monomorphic

data ⊥ : Type ℓ where

Poly⊥⇔Mono⊥ : ⊥ ⇔ Monomorphic.⊥
Poly⊥⇔Mono⊥ .fun      ()
Poly⊥⇔Mono⊥ .inv      ()
Poly⊥⇔Mono⊥ .leftInv  ()
Poly⊥⇔Mono⊥ .rightInv ()
