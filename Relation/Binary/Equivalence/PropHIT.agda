{-# OPTIONS --cubical --safe #-}

module Relation.Binary.Equivalence.PropHIT where

open import Prelude
open import Relation.Nullary.Stable
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar
open import Relation.Binary

infix 4 _≐_
_≐_ : A → A → Type _
x ≐ y = ∥ x ≡ y ∥

import Relation.Binary.Equivalence.Reasoning

module _ {A : Type a} where
  prop-equiv : Equivalence A _
  prop-equiv .Equivalence._≋_ = _≐_
  prop-equiv .Equivalence.sym = sym ∥$∥_
  prop-equiv .Equivalence.refl = ∣ refl ∣
  prop-equiv .Equivalence.trans x≐y y≐z = ⦇ x≐y ; y≐z ⦈

  module Reasoning = Relation.Binary.Equivalence.Reasoning prop-equiv

-- data ∙⊥ : Prop where

-- private
--   variable
--     x y z : A

-- rerel : ∙⊥ → ⊥
-- rerel ()

-- ∙refute : x ≐ y → (x ≡ y → ⊥) → ∙⊥
-- ∙refute ∣ x≡y ∣ x≢y with x≢y x≡y
-- ∙refute ∣ x≡y ∣ x≢y | ()

-- refute : x ≐ y → ¬ (¬ (x ≡ y))
-- refute x≐y x≢y = rerel (∙refute x≐y x≢y)

-- unsquash : Stable (x ≡ y) → x ≐ y → x ≡ y
-- unsquash st x≐y = st (refute x≐y)

-- ∙refl : x ≐ x
-- ∙refl = ∣ refl ∣

-- ∙trans : x ≐ y → y ≐ z → x ≐ z
-- ∙trans ∣ xy ∣ (∣_∣ yz) = ∣_∣ (xy ; yz)

-- ∙sym : x ≐ y → y ≐ x
-- ∙sym (∣_∣ p) = ∣_∣ (sym p)

-- ∙cong : (f : A → B) → x ≐ y → f x ≐ f y
-- ∙cong f ∣ x≡y ∣ = ∣ cong f x≡y ∣


-- module Reasoning where
--   infixr 2 ≐˘⟨⟩-syntax ≐⟨∙⟩-syntax

--   ≐˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≐ z → y ≐ x → x ≐ z
--   ≐˘⟨⟩-syntax _ y≡z y≡x = ∙trans (∙sym y≡x) y≡z

--   syntax ≐˘⟨⟩-syntax x y≡z y≡x = x ≐˘⟨ y≡x ⟩ y≡z

--   ≐⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≐ z → x ≐ y → x ≐ z
--   ≐⟨∙⟩-syntax _ y≡z x≡y = ∙trans x≡y y≡z

--   syntax ≐⟨∙⟩-syntax x y≡z x≡y = x ≐⟨ x≡y ⟩ y≡z

--   _≐⟨⟩_ : ∀ (x : A) {y} → x ≐ y → x ≐ y
--   _ ≐⟨⟩ x≡y = x≡y

--   infix 2.5 _∎
--   _∎ : ∀ {A : Type a} (x : A) → x ≐ x
--   _∎ x = ∙refl

--   infixr 2 ≡˘⟨⟩-syntax ≡⟨∙⟩-syntax

--   ≡˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≐ z → y ≡ x → x ≐ z
--   ≡˘⟨⟩-syntax _ y≡z y≡x = ∙trans (∣_∣ (sym y≡x)) y≡z

--   syntax ≡˘⟨⟩-syntax x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

--   ≡⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≐ z → x ≡ y → x ≐ z
--   ≡⟨∙⟩-syntax _ y≡z x≡y = ∙trans ∣ x≡y ∣ y≡z

--   syntax ≡⟨∙⟩-syntax x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z
