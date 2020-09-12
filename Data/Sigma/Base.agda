{-# OPTIONS --cubical --safe #-}

module Data.Sigma.Base where

open import Agda.Builtin.Sigma
  using (Σ; _,_; fst; snd)
  public
open import Level
open import Path

∃ : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃ {A = A} = Σ A

infixr 4.5 ∃-syntax
∃-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → e) = ∃[ x ] e

infixr 4.5 Σ⦂-syntax
Σ⦂-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ⦂-syntax = Σ

syntax Σ⦂-syntax t (λ x → e) = Σ[ x ⦂ t ] e

infixr 4.5 _×_
_×_ : (A : Type a) → (B : Type b) → Type (a ℓ⊔ b)
A × B = Σ A λ _ → B

curry : ∀ {A : Type a} {B : A → Type b} {C : Σ A B → Type c} →
          ((p : Σ A B) → C p) →
          ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {A : Type a} {B : A → Type b} {C : Σ A B → Type c} →
            ((x : A) → (y : B x) → C (x , y)) →
            ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

map-Σ : ∀ {p q} {P : A → Set p} {Q : B → Set q} →
        (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
map-Σ f g (x , y) = (f x , g y)

map₁ : (A → B) → A × C → B × C
map₁ f = map-Σ f (λ x → x)

map₁-Σ : ∀ {A : Set a} {B : Set b} {C : B → Set b}
       → (f : A → B) → Σ A (λ x → C (f x)) → Σ B C
map₁-Σ f (x , y) = f x , y

map₂ : ∀ {A : Set a} {B : A → Set b} {C : A → Set c} →
        (∀ {x} → B x → C x) → Σ A B → Σ A C
map₂ f = map-Σ (λ x → x) f

∃! : ∀ {a b} {A : Type a} → (A → Type b) → Type (a ℓ⊔ b)
∃! B = ∃ λ x → B x × (∀ {y} → B y → x ≡ y)

infixr 4.5 ∃!-syntax
∃!-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃!-syntax = ∃!

syntax ∃!-syntax (λ x → e) = ∃![ x ] e
