{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Algebra

module Data.FingerTree {ℓ} (mon : Monoid ℓ) where

open Monoid mon

record Measured {a} (A : Type a) : Type (a ℓ⊔ ℓ) where
  constructor measured
  field μ : A → 𝑆

open Measured ⦃ ... ⦄ public

data Digit {a} (A : Type a) : Type a where
  D₁ : A → Digit A
  D₂ : A → A → Digit A
  D₃ : A → A → A → Digit A

data Node {a} (A : Type a) : Type a where
  N₂ : A → A → Node A
  N₃ : A → A → A → Node A

instance
  measuredDigit : ⦃ _ : Measured A ⦄ → Measured (Digit A)
  measuredDigit =
    measured λ { (D₁ x) → μ x
               ; (D₂ x x₁) → μ x ∙ μ x₁
               ; (D₃ x x₁ x₂) → μ x ∙ μ x₁ ∙ μ x₂
               }

instance
  measuredNode : ⦃ _ : Measured A ⦄ → Measured (Node A)
  measuredNode =
    measured λ { (N₂ x x₁) → μ x ∙ μ x₁
               ; (N₃ x x₁ x₂) → μ x ∙ μ x₁ ∙ μ x₂
               }

record ⟪_⟫ (A : Type a) ⦃ _ : Measured A ⦄ : Type (a ℓ⊔ ℓ) where
  constructor recd
  field
    val : A
    mem : 𝑆
    prf : μ val ≡ mem
open ⟪_⟫ public

memo : ⦃ _ : Measured A ⦄ → A → ⟪ A ⟫
memo x = recd x (μ x) refl

instance
  measuredMemo : ⦃ _ : Measured A ⦄ → Measured ⟪ A ⟫
  measuredMemo = measured mem

mutual
  record Deep {a} (A : Type a) ⦃ _ : Measured A ⦄ : Type (a ℓ⊔ ℓ) where
    constructor more
    inductive
    field
      lbuff : Digit A
      tree  : Tree ⟪ Node A ⟫
      rbuff : Digit A

  data Tree {a} (A : Type a) ⦃ _ : Measured A ⦄ : Type (a ℓ⊔ ℓ) where
    empty : Tree A
    single : A → Tree A
    deep : ⟪ Deep A ⟫  → Tree A

  μ-deep : ∀ {a} {A : Type a} ⦃ _ : Measured A ⦄ → Deep A → 𝑆
  μ-deep (more l x r) = μ l ∙ (μ-tree x ∙ μ r)

  μ-tree : ∀ {a} {A : Type a} ⦃ _ : Measured A ⦄ → Tree A → 𝑆
  μ-tree empty = ε
  μ-tree (single x) = μ x
  μ-tree (deep xs) = xs .mem

  instance
    Measured-Deep : ∀ {a} {A : Type a} → ⦃ _ : Measured A ⦄ → Measured (Deep A)
    Measured-Deep = measured μ-deep

  instance
    Measured-Tree : ∀ {a} {A : Type a} → ⦃ _ : Measured A ⦄ → Measured (Tree A)
    Measured-Tree = measured μ-tree
open Deep
