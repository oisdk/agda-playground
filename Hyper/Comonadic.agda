{-# OPTIONS --no-termination-check #-}

open import Prelude
open import Algebra

module Hyper.Comonadic {g} {𝐺 : Type g → Type g} (comon : Comonad 𝐺) where

open Comonad comon

infixr 0 _↬_ _↬′_
_↬′_ : Type g → Type g → Type g


{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type g) (B : Type g) : Type g where
  inductive
  infixl 4 _·_
  field _·_ : 𝐺 (B ↬′ A) → B
open _↬_

A ↬′ B = B ↬ A → B

infixr 9 _⊙_ _⊙′_
mutual
  _⊙′_ : B ↬ C → 𝐺 (A ↬′ B) → 𝐺 (A ↬′ C)
  f ⊙′ g = extend (λ g′ g″ → f · cmap (λ f′ k → f′ (g″ ⊙ k)) g′) g

  _⊙_ : B ↬ C → A ↬ B → A ↬ C
  (f ⊙ g) · k = f · (g ⊙′ k)

𝕀 : A ↬ A
𝕀 · x = extract x 𝕀

_◃_ : (𝐺 A → B) → A ↬ B → A ↬ B
(f ◃ h) · k = f (cmap (_$ h) k)

△ : (𝐺 A → B) → A ↬ B
△ f = f ◃ (△ f)

k : A → B ↬ A
k x · _ = x

▽ : A ↬ B → 𝐺 A → B
▽ h x = h · cmap const x

cata : {C : Type g} → ((𝐺 (C → A) → B) → C) → A ↬ B → C
cata ϕ h = ϕ λ k → h · cmap (_∘ cata ϕ) k

ana : {C : Type g} → (C → 𝐺 (C → A) → B) → C → A ↬ B
ana ψ r · k = ψ r (cmap (_∘ ana ψ) k)

_◂_▸_ : ∀ {A′ B′} → (𝐺 B → B′) → A ↬ B → (𝐺 A′ → A) → A′ ↬ B′
f ◂ h ▸ g = △ f ⊙ h ⊙ △ g
