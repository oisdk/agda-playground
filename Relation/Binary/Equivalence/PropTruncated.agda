{-# OPTIONS --cubical --safe --prop #-}

module Relation.Binary.Equivalence.PropTruncated where

open import Agda.Primitive using (Prop)
open import Prelude
open import Relation.Nullary.Stable

infix 4 _≐_
data _≐_ {a} {A : Type a} (x y : A) : Prop a where
  ∣_∣ : x ≡ y → x ≐ y

data ∙⊥ : Prop where

private
  variable
    x y z : A

rerel : ∙⊥ → ⊥
rerel ()

∙refute : x ≐ y → (x ≡ y → ⊥) → ∙⊥
∙refute ∣ x≡y ∣ x≢y with x≢y x≡y
∙refute ∣ x≡y ∣ x≢y | ()

refute : x ≐ y → ¬ (¬ (x ≡ y))
refute x≐y x≢y = rerel (∙refute x≐y x≢y)

unsquash : Stable (x ≡ y) → x ≐ y → x ≡ y
unsquash st x≐y = st (refute x≐y)

∙refl : x ≐ x
∙refl = ∣ refl ∣

∙trans : x ≐ y → y ≐ z → x ≐ z
∙trans ∣ xy ∣ ∣ yz ∣ = ∣ xy ; yz ∣

∙sym : x ≐ y → y ≐ x
∙sym ∣ p ∣ = ∣ sym p ∣

∙cong : (f : A → B) → x ≐ y → f x ≐ f y
∙cong f ∣ x≡y ∣ = ∣ cong f x≡y ∣


module Reasoning where
  infixr 2 ≐˘⟨⟩-syntax ≐⟨∙⟩-syntax

  ≐˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≐ z → y ≐ x → x ≐ z
  ≐˘⟨⟩-syntax _ y≡z y≡x = ∙trans (∙sym y≡x) y≡z

  syntax ≐˘⟨⟩-syntax x y≡z y≡x = x ≐˘⟨ y≡x ⟩ y≡z

  ≐⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≐ z → x ≐ y → x ≐ z
  ≐⟨∙⟩-syntax _ y≡z x≡y = ∙trans x≡y y≡z

  syntax ≐⟨∙⟩-syntax x y≡z x≡y = x ≐⟨ x≡y ⟩ y≡z

  _≐⟨⟩_ : ∀ (x : A) {y} → x ≐ y → x ≐ y
  _ ≐⟨⟩ x≡y = x≡y

  infix 2.5 _∎
  _∎ : ∀ {A : Type a} (x : A) → x ≐ x
  _∎ x = ∙refl

  infixr 2 ≡˘⟨⟩-syntax ≡⟨∙⟩-syntax

  ≡˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≐ z → y ≡ x → x ≐ z
  ≡˘⟨⟩-syntax _ y≡z y≡x = ∙trans ∣ sym y≡x ∣ y≡z

  syntax ≡˘⟨⟩-syntax x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

  ≡⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≐ z → x ≡ y → x ≐ z
  ≡⟨∙⟩-syntax _ y≡z x≡y = ∙trans ∣ x≡y ∣ y≡z

  syntax ≡⟨∙⟩-syntax x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z
