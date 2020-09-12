{-# OPTIONS --cubical --safe #-}

open import Relation.Binary

module Relation.Binary.Equivalence.Reasoning {a} {𝑆 : Set a} {b} (equivalence : Equivalence 𝑆 b) where

open Equivalence equivalence
open import Function

import Path

infixr 2 ≋˘⟨⟩-syntax _≋⟨⟩_ ≋⟨∙⟩-syntax ≡⟨∙⟩-syntax

≋˘⟨⟩-syntax : ∀ (x : 𝑆) {y z} → y ≋ z → y ≋ x → x ≋ z
≋˘⟨⟩-syntax _ y≋z y≋x = sym y≋x ⟨ trans ⟩ y≋z

syntax ≋˘⟨⟩-syntax x y≋z y≋x = x ≋˘⟨ y≋x ⟩ y≋z

≋⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≋ z → x ≋ y → x ≋ z
≋⟨∙⟩-syntax _ y≋z x≋y = x≋y ⟨ trans ⟩ y≋z

syntax ≋⟨∙⟩-syntax x y≋z x≋y = x ≋⟨ x≋y ⟩ y≋z

_≋⟨⟩_ : ∀ (x : 𝑆) {y} → x ≋ y → x ≋ y
_ ≋⟨⟩ x≋y = x≋y

≡⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≋ z → x Path.≡ y → x ≋ z
≡⟨∙⟩-syntax _ y≋z x≡y = Path.subst (_≋ _) (Path.sym x≡y) y≋z

syntax ≡⟨∙⟩-syntax x y≋z x≡y = x ≡⟨ x≡y ⟩ y≋z

infix 2.5 _∎
_∎ : ∀ x → x ≋ x
x ∎ = refl
