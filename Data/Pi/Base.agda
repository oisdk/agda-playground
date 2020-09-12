{-# OPTIONS --safe --cubical #-}

module Data.Pi.Base where

open import Level

Π : (A : Type a) (B : A → Type b) → Type _
Π A B = (x : A) → B x

∀′ : {A : Type a} (B : A → Type b) → Type _
∀′ {A = A} B = Π A B

infixr 4.5 ∀-syntax
∀-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∀-syntax = ∀′

syntax ∀-syntax (λ x → e) = ∀[ x ] e

infixr 4.5 Π⦂-syntax
Π⦂-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Π⦂-syntax = Π

syntax Π⦂-syntax t (λ x → e) = Π[ x ⦂ t ] e
