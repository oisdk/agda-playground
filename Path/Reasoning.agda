{-# OPTIONS --cubical --safe #-}

module Path.Reasoning where

open import Prelude

infixr 2 ≡˘⟨⟩-syntax _≡⟨⟩_ ≡⟨∙⟩-syntax ≡⟨∙⟩[∙]-syntax

≡˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≡ z → y ≡ x → x ≡ z
≡˘⟨⟩-syntax _ y≡z y≡x = sym y≡x ; y≡z

syntax ≡˘⟨⟩-syntax x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

≡⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨∙⟩-syntax _ y≡z x≡y = x≡y ; y≡z

syntax ≡⟨∙⟩-syntax x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

_≡⟨⟩_ : ∀ (x : A) {y} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

infix 2.5 _∎
_∎ : ∀ {A : Type a} (x : A) → x ≡ x
_∎ x = refl

≡⟨∙⟩[∙]-syntax : ∀ (x : A) {x′ y′ : B} {y z} → y ≡ z → x′ ≡ y′ → (x′ ≡ y′ → x ≡ y) → x ≡ z
≡⟨∙⟩[∙]-syntax _ y≡z x′≡y′ x′≡y′⇒x≡y = x′≡y′⇒x≡y x′≡y′ ; y≡z

syntax ≡⟨∙⟩[∙]-syntax x y≡z x′≡y′ x′≡y′⇒x≡y = x ≡⟨ x′≡y′⇒x≡y ⟩[ x′≡y′ ] y≡z

infixr 2 begin-syntax
begin-syntax : {x y : A} → x ≡ y → x ≡ y
begin-syntax f i = f i

syntax begin-syntax f i = begin[ i ] f
