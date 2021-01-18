{-# OPTIONS --cubical --safe #-}

module Container.Polynomial where

open import Prelude hiding (id; const; _×_; Π; _⊎_; Σ; _∘_; ⊤; ⊥)

open import Data.Unit.UniversePolymorphic
open import Data.Empty.UniversePolymorphic

import Prelude as P
open import Container

module _ {s p : Level} where

  id : Container s p
  id .fst = ⊤
  id .snd _ = ⊤

  const : Type s → Container s p
  const X .fst = X
  const X .snd _ = ⊥

infixr 9 _∘_

_∘_ : ∀ {s₁ s₂ p₁ p₂} → Container s₁ p₁ → Container s₂ p₂ →
      Container (s₁ ℓ⊔ s₂ ℓ⊔ p₁) (p₁ ℓ⊔ p₂)
(C₁ ∘ C₂) .fst = ⟦ C₁ ⟧ (fst C₂)
(C₁ ∘ C₂) .snd cx = ∃ (snd C₂ P.∘ snd cx)

infixr 2 _×_

_×_ : ∀ {s₁ s₂ p₁ p₂} → Container s₁ p₁ → Container s₂ p₂ →
      Container (s₁ ℓ⊔ s₂) (p₁ ℓ⊔ p₂)
(C₁ × C₂) .fst = fst C₁ P.× fst C₂
(C₁ × C₂) .snd = P.uncurry λ s₁ s₂ → (snd C₁ s₁) P.⊎ (snd C₂ s₂)

Π : ∀ {i s p} (I : Type i) → (I → Container s p) → Container (i ℓ⊔ s) (i ℓ⊔ p)
Π I C .fst = ∀ i → fst (C i)
Π I C .snd = λ s → ∃ λ i → snd (C i) (s i)

infix 0 const[_]⟶_

const[_]⟶_ : ∀ {i s p} → Type i → Container s p → Container (i ℓ⊔ s) (i ℓ⊔ p)
const[ X ]⟶ C = Π X (P.const C)

infixr 1 _⊎_

_⊎_ : ∀ {s₁ s₂ p} → Container s₁ p → Container s₂ p → Container (s₁ ℓ⊔ s₂) p
(C₁ ⊎ C₂) .fst = (fst C₁ P.⊎ fst C₂)
(C₁ ⊎ C₂) .snd = either (snd C₁) (snd C₂)

Σ : ∀ {i s p} (I : Type i) → (I → Container s p) → Container (i ℓ⊔ s) p
Σ I C .fst = ∃ λ i → fst (C i)
Σ I C .snd s = snd (C (fst s)) (snd s)
