{-# OPTIONS --cubical --safe #-}

module Container.Polynomial where

open import Prelude hiding (id; const; _×_; Π; _⊎_; Σ; _∘_; ⊤; ⊥)

open import Data.Unit.UniversePolymorphic
open import Data.Empty.UniversePolymorphic

import Prelude as P
open import Container


id : Container
id .fst = ⊤
id .snd _ = ⊤

const : Type  → Container
const X .fst = X
const X .snd _ = ⊥

infixr 9 _∘_

_∘_ : Container → Container →
      Container
(C₁ ∘ C₂) .fst = ⟦ C₁ ⟧ (fst C₂)
(C₁ ∘ C₂) .snd cx = ∃ x × (snd C₂ P.∘ snd cx) x

infixr 2 _×_

_×_ : Container → Container → Container
(C₁ × C₂) .fst = fst C₁ P.× fst C₂
(C₁ × C₂) .snd = P.uncurry λ s₁ s₂ → (snd C₁ s₁) P.⊎ (snd C₂ s₂)

Π : (I : Type) → (I → Container ) → Container
Π I C .fst = ∀ i → fst (C i)
Π I C .snd = λ s → ∃ i × snd (C i) (s i)

infix 0 const[_]⟶_

const[_]⟶_ : Type → Container → Container
const[ X ]⟶ C = Π X (P.const C)

infixr 1 _⊎_

_⊎_ : Container → Container → Container
(C₁ ⊎ C₂) .fst = (fst C₁ P.⊎ fst C₂)
(C₁ ⊎ C₂) .snd = either (snd C₁) (snd C₂)

Σ : (I : Type) → (I → Container) → Container
Σ I C .fst = ∃ i × fst (C i)
Σ I C .snd s = snd (C (fst s)) (snd s)
