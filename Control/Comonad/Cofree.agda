{-# OPTIONS --no-positivity-check --allow-unsolved-metas #-}

open import Prelude
open import Algebra

module Control.Comonad.Cofree
  where

module Comonadic
  {ℓ₁ ℓ₂}
  (mon : Monoid ℓ₁)
  (comon : GradedComonad mon ℓ₂)
  {𝐹 : Type (ℓ₁ ℓ⊔ ℓ₂) → Type ℓ₂}
  (functor : Functor 𝐹) where

  open Monoid mon
  open GradedComonad comon renaming (𝐹 to 𝑊; map to cmap)
  open Functor functor renaming (map to fmap)

  record CofreeF (A : Type ℓ₂) : Type ℓ₂ where
    constructor _◃_
    coinductive
    field
      head : A
      step : 𝐹 (∃ y × 𝑊 y (CofreeF A))
  open CofreeF public

  Cofree : Type ℓ₂ → Type ℓ₂
  Cofree A = 𝑊 ε (CofreeF A)

  extract′ : Cofree A → A
  extract′ = head ∘ extract

  {-# TERMINATING #-}
  extend′ : ∀ {x} → (Cofree A → B) → 𝑊 x (CofreeF A) → 𝑊 x (CofreeF B)
  extend′ k xs = xs =>>[ ∙ε _ ] (λ x → k x ◃ fmap (map₂ (extend′ k)) (step (extract x)))

module Monadic
  {ℓ₁ ℓ₂ ℓ₃}
  (mon : Monoid ℓ₁)
  (monad : GradedMonad mon ℓ₂ ℓ₃)
  {𝐹 : Type (ℓ₁ ℓ⊔ ℓ₃) → Type ℓ₂}
  (alternative : Alternative 𝐹) where

  open Monoid mon
  open GradedMonad monad renaming (𝐹 to 𝑀; map to mmap)
  open Alternative alternative renaming (map to fmap)

  record CofreeF (A : Type ℓ₂) : Type ℓ₂ where
    pattern
    constructor _◃_
    inductive
    field
      head : A
      step : 𝐹 (∃ y × 𝑀 y (CofreeF A))
  open CofreeF public

  Cofree : Type ℓ₂ → Type ℓ₃
  Cofree A = 𝑀 ε (CofreeF A)

  return′ : A → Cofree A
  return′ x = return (x ◃ 0#)

  {-# TERMINATING #-}
  bind′ : ∀ {x} → (A → Cofree B) → 𝑀 x (CofreeF A) → 𝑀 x (CofreeF B)
  bind′ k xs = xs >>=[ ∙ε _ ]
    λ { (x ◃ xs) → mmap (λ { (y ◃ ys) →  y ◃ (ys <|> fmap (map₂ (bind′ k)) xs) }) (k x) }


