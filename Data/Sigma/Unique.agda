{-# OPTIONS --cubical --safe #-}

module Data.Sigma.Unique where

open import Data.Sigma.Base
open import Level
open import Path

∃! : ∀ {a b} {A : Type a} → (A → Type b) → Type (a ℓ⊔ b)
∃! B = ∃ λ x → B x × (∀ {y} → B y → x ≡ y)

infixr 4.5 ∃!-syntax
∃!-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃!-syntax = ∃!

syntax ∃!-syntax (λ x → e) = ∃![ x ] e
