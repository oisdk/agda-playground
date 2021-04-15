{-# OPTIONS --without-K --safe #-}

module Function.Reasoning where

open import Level

infixr 2 _⟨⟩⇒_ ⟨∙⟩⇒-syntax

⟨∙⟩⇒-syntax : ∀ (A : Type a) → (B → C) → (A → B) → A → C
⟨∙⟩⇒-syntax _ f g x = f (g x)

syntax ⟨∙⟩⇒-syntax A f g = A ⟨ g ⟩⇒ f

_⟨⟩⇒_ : ∀ (A : Type a) → (A → B) → A → B
_ ⟨⟩⇒ f = f

infix 2.5 _⇒∎
_⇒∎ : (A : Type a) → A → A
_⇒∎ _ x = x

infixr 1.5 [_]⇒_
[_]⇒_ : A → (A → B) → B
[ x ]⇒ f = f x

-- infix 2.5 _⇒[_]
-- _⇒[_] : (A : Type a) → A → A
-- _ ⇒[ x ] = x
