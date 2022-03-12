{-# OPTIONS --safe --cubical --postfix-projections #-}

module Relation.Binary where

open import Level

open import Function using (_∘_; flip; id)
open import Inspect  using (inspect;〖_〗)

open import HLevels   using (isSet)
open import Path as ≡ hiding (sym; refl)

open import Data.Bool            using (Bool; true; false; bool)
open import Data.Bool.Properties using (false≢true)
open import Data.Empty           using (⊥; ⊥-elim; ¬_)
open import Data.Sum             using (either; inl; inr; _⊎_; is-l)

open import Relation.Nullary.Decidable            using (Dec; yes; no; does)
open import Relation.Nullary.Decidable.Properties using (Dec→Stable)
open import Relation.Nullary.Discrete             using (Discrete)
open import Relation.Nullary.Discrete.Properties  using (Discrete→isSet)
open import Relation.Nullary.Stable               using (Stable)

module _ (_~_ : A → A → Type b) where
  Reflexive : Type _
  Reflexive = ∀ {x} → x ~ x

  Transitive : Type _
  Transitive = ∀ {x y z} → x ~ y → y ~ z → x ~ z

  Symmetric : Type _
  Symmetric = ∀ {x y} → x ~ y → y ~ x

  Decidable : Type _
  Decidable = ∀ x y → Dec (x ~ y)

  Antisymmetric : Type _
  Antisymmetric = ∀ {x y} → x ~ y → y ~ x → x ≡ y

  Connected : Type _
  Connected = ∀ {x y} → ¬ (x ~ y) → ¬ (y ~ x) → x ≡ y

  Asymmetric : Type _
  Asymmetric = ∀ {x y} → x ~ y → ¬ (y ~ x)

  Irreflexive : Type _
  Irreflexive = ∀ {x} → ¬ (x ~ x)

  Total : Type _
  Total = ∀ x y → (x ~ y) ⊎ (y ~ x)

record Preorder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  infix 4 _≤_
  field
    _≤_ : 𝑆 → 𝑆 → Type ℓ₂
    refl : Reflexive _≤_
    trans : Transitive _≤_

  infix 4 _≰_ _≥_ _≱_
  _≰_ _≥_ _≱_ : 𝑆 → 𝑆 → Type ℓ₂
  x ≰ y = ¬ (x ≤ y)
  x ≥ y = y ≤ x
  x ≱ y = ¬ (y ≤ x)

record StrictPreorder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  infix 4 _<_
  field
    _<_ : 𝑆 → 𝑆 → Type ℓ₂
    trans : Transitive _<_
    irrefl : Irreflexive _<_

  asym : Asymmetric _<_
  asym x<y y<x = irrefl (trans x<y y<x)

  infix 4 _≮_ _>_ _≯_
  _≮_ _>_ _≯_ : 𝑆 → 𝑆 → Type ℓ₂
  x ≮ y = ¬ (x < y)
  x > y = y < x
  x ≯ y = ¬ (y < x)

record StrictPartialOrder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  field strictPreorder : StrictPreorder 𝑆 ℓ₂
  open StrictPreorder strictPreorder public
  field conn : Connected _<_

record PartialOrder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  field preorder : Preorder 𝑆 ℓ₂
  open Preorder preorder public
  field antisym : Antisymmetric _≤_

data Tri (A : Type a) (B : Type b) (C : Type c) : Type (a ℓ⊔ b ℓ⊔ c) where
  lt : (x<y : A) → Tri A B C
  eq : (x≡y : B) → Tri A B C
  gt : (x>y : C) → Tri A B C

record TotalOrder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ ℓ₃ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂ ℓ⊔ ℓsuc ℓ₃) where
  field
    strictPartialOrder : StrictPartialOrder 𝑆 ℓ₂
    partialOrder : PartialOrder 𝑆 ℓ₃
  open PartialOrder partialOrder renaming (trans to ≤-trans) public
  open StrictPartialOrder strictPartialOrder renaming (trans to <-trans) public

  infix 4 _<?_
  field
    _<?_ : Decidable _<_

    ≰⇒> : ∀ {x y} → x ≰ y → x > y
    ≮⇒≥ : ∀ {x y} → x ≮ y → x ≥ y

  <⇒≤ : ∀ {x y} → x < y → x ≤ y
  <⇒≤ = ≮⇒≥ ∘ asym

  _<ᵇ_ : 𝑆 → 𝑆 → Bool
  x <ᵇ y = does (x <? y)

  <⇒≱ : ∀ {x y} → x < y → x ≱ y
  <⇒≱ {x} {y} x<y x≥y = irrefl (subst (_< _) (antisym (<⇒≤ x<y) x≥y) x<y)

  ≤⇒≯ : ∀ {x y} → x ≤ y → x ≯ y
  ≤⇒≯ {x} {y} x≤y x>y = irrefl (subst (_< _) (antisym (≮⇒≥ (asym x>y)) x≤y) x>y)

  infix 4 _≤ᵇ_ _≤?_ _≤|≥_ _≟_

  _≤?_ : Decidable _≤_
  x ≤? y with y <? x
  ... | yes y<x = no  (<⇒≱ y<x)
  ... | no  y≮x = yes (≮⇒≥ y≮x)

  _≤ᵇ_ : 𝑆 → 𝑆 → Bool
  x ≤ᵇ y = does (x ≤? y)

  _≤|≥_ : Total _≤_
  x ≤|≥ y with x <? y
  ... | yes x<y = inl (<⇒≤ x<y)
  ... | no  x≮y = inr (≮⇒≥ x≮y)

  _≟_ : Discrete 𝑆
  x ≟ y with x <? y | y <? x
  ... | yes x<y | _ = no (λ x≡y → irrefl (subst (_< _) x≡y x<y))
  ... | _ | yes y<x = no (λ x≡y → irrefl (subst (_ <_) x≡y y<x))
  ... | no x≮y | no y≮x = yes (conn x≮y y≮x)

  Ordering : (x y : 𝑆) → Type (ℓ₁ ℓ⊔  ℓ₂)
  Ordering x y = Tri (x < y) (x ≡ y) (x > y)

  compare : ∀ x y → Ordering x y
  compare x y with x <? y | y <? x
  ... | yes x<y | _ = lt x<y
  ... | no  x≮y | yes y<x = gt y<x
  ... | no  x≮y | no  y≮x = eq (conn x≮y y≮x)

  total⇒isSet : isSet 𝑆
  total⇒isSet = Discrete→isSet _≟_

  data _≲_ (x y : 𝑆) : Type (ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃) where
    <[_] : (x<y : x < y) → x ≲ y
    ≤[_] : (x≤y : x ≤ y) → x ≲ y
    ≡[_] : (x≡y : x ≡ y) → x ≲ y

  Ordℓ : ∀ {x y} → x ≲ y → Level
  Ordℓ <[ _ ] = ℓ₂
  Ordℓ ≤[ _ ] = ℓ₃
  Ordℓ ≡[ _ ] = ℓ₁

  TheOrd : ∀ {x y} → (x≲y : x ≲ y) → Type (Ordℓ x≲y)
  TheOrd {x} {y} <[ _ ] = x < y
  TheOrd {x} {y} ≤[ _ ] = x ≤ y
  TheOrd {x} {y} ≡[ _ ] = x ≡ y

  ≲[_] : ∀ {x y} → (x≲y : x ≲ y) → TheOrd x≲y
  ≲[ <[ x<y ] ] = x<y
  ≲[ ≤[ x≤y ] ] = x≤y
  ≲[ ≡[ x≡y ] ] = x≡y

  ≱[_] : ∀ {x y} → x ≱ y → x ≲ y
  ≱[ x≱y ] = <[ ≰⇒> x≱y ]

  ≯[_] : ∀ {x y} → x ≯ y → x ≲ y
  ≯[ x≯y ] = ≤[ ≮⇒≥ x≯y ]

  infixr 2 _≲;_

  _≲;_ : ∀ {x y z} → x ≲ y → y ≲ z → x ≲ z
  <[ x≲y ] ≲; <[ y≲z ] = <[ <-trans x≲y y≲z ]
  <[ x≲y ] ≲; ≡[ y≲z ] = <[ subst (_ <_) y≲z x≲y ]
  ≡[ x≲y ] ≲; <[ y≲z ] = <[ subst (_< _) (≡.sym x≲y) y≲z ]
  ≡[ x≲y ] ≲; ≡[ y≲z ] = ≡[ x≲y ; y≲z ]
  ≡[ x≲y ] ≲; ≤[ y≲z ] = ≤[ subst (_≤ _) (≡.sym x≲y) y≲z ]
  ≤[ x≲y ] ≲; ≤[ y≲z ] = ≤[ ≤-trans x≲y y≲z ]
  ≤[ x≲y ] ≲; ≡[ y≲z ] = ≤[ subst (_ ≤_) y≲z x≲y ]
  ≤[ x≲y ] ≲; <[ y≲z ] = ≱[ (λ z≤x → <⇒≱ y≲z (≤-trans z≤x x≲y)) ]
  <[ x≲y ] ≲; ≤[ y≲z ] = ≱[ (λ z≤x → <⇒≱ x≲y (≤-trans y≲z z≤x)) ]

  module Reasoning where

    infixr 2 ≤⟨∙⟩-syntax <⟨∙⟩-syntax ≡⟨∙⟩-syntax ≡˘⟨∙⟩-syntax _≡⟨⟩_ ≱⟨∙⟩-syntax ≯⟨∙⟩-syntax

    ≤⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≲ z → x ≤ y → x ≲ z
    ≤⟨∙⟩-syntax _ y≲z x≤y = ≤[ x≤y ] ≲; y≲z

    syntax ≤⟨∙⟩-syntax x y≲z x≤y = x ≤⟨ x≤y ⟩ y≲z

    ≱⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≲ z → x ≱ y → x ≲ z
    ≱⟨∙⟩-syntax _ y≲z x≱y = ≱[ x≱y ] ≲; y≲z

    syntax ≱⟨∙⟩-syntax x y≲z x≱y = x ≱⟨ x≱y ⟩ y≲z

    <⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≲ z → x < y → x ≲ z
    <⟨∙⟩-syntax _ y≲z x<y = <[ x<y ] ≲; y≲z

    syntax <⟨∙⟩-syntax x y≲z x<y = x <⟨ x<y ⟩ y≲z

    ≯⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≲ z → x ≯ y → x ≲ z
    ≯⟨∙⟩-syntax _ y≲z x≯y = ≯[ x≯y ] ≲; y≲z

    syntax ≯⟨∙⟩-syntax x y≲z x≯y = x ≯⟨ x≯y ⟩ y≲z

    ≡⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≲ z → x ≡ y → x ≲ z
    ≡⟨∙⟩-syntax _ y≲z x≡y = ≡[ x≡y ] ≲; y≲z

    syntax ≡⟨∙⟩-syntax x y≲z x≡y = x ≡⟨ x≡y ⟩ y≲z

    ≡˘⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≲ z → y ≡ x → x ≲ z
    ≡˘⟨∙⟩-syntax _ y≲z y≡x = ≡[ ≡.sym y≡x ] ≲; y≲z

    syntax ≡˘⟨∙⟩-syntax x y≲z y≡x = x ≡˘⟨ y≡x ⟩ y≲z

    _≡⟨⟩_ : ∀ (x : 𝑆) {y} → x ≲ y → x ≲ y
    _ ≡⟨⟩ x≲y = x≲y

    infix 2.5 _∎
    _∎ : ∀ x → x ≲ x
    x ∎ = ≡[ ≡.refl ]

    infixr 2 begin_
    begin_ = ≲[_]

    _ : ∀ w x y z → w < x → x ≡ y → y ≤ z → w < z
    _ = λ w x y z w<x x≡y y≤z → begin
      w <⟨ w<x ⟩
      x ≡⟨ x≡y ⟩
      y ≤⟨ y≤z ⟩
      z ∎

module FromPartialOrder {ℓ₁} {𝑆 : Type ℓ₁} {ℓ₂} (po : PartialOrder 𝑆 ℓ₂) (_≤|≥_ : Total (PartialOrder._≤_ po)) where
  open PartialOrder po

  partialOrder = po

  ≤-side : 𝑆 → 𝑆 → Bool
  ≤-side x y = is-l (x ≤|≥ y)

  ≤-dec : Decidable _≤_
  ≤-dec x y with x ≤|≥ y | y ≤|≥ x | inspect (≤-side x) y | inspect (≤-side y) x
  ≤-dec x y | inl x≤y | _       | _ | _ = yes x≤y
  ≤-dec x y | inr x≥y | inr y≥x | _ | _ = yes y≥x
  ≤-dec x y | inr x≥y | inl y≤x | 〖 x≥yᵇ 〗 | 〖 y≤xᵇ 〗 = no (x≢y ∘ flip antisym x≥y)
    where
    x≢y : x ≢ y
    x≢y x≡y = false≢true (≡.sym x≥yᵇ ; cong₂ ≤-side x≡y (≡.sym x≡y) ; y≤xᵇ)

  ≮⇒≥ : ∀ {x y} → Stable (x ≤ y)
  ≮⇒≥ {x} {y} = Dec→Stable _ (≤-dec x y)

  strictPartialOrder : StrictPartialOrder 𝑆 ℓ₂
  strictPartialOrder .StrictPartialOrder.strictPreorder .StrictPreorder._<_ x y = ¬ (y ≤ x)
  strictPartialOrder .StrictPartialOrder.conn x<y y<x = antisym (≮⇒≥ y<x) (≮⇒≥ x<y)
  strictPartialOrder .StrictPartialOrder.strictPreorder .StrictPreorder.irrefl y≰x = y≰x refl
  strictPartialOrder .StrictPartialOrder.strictPreorder .StrictPreorder.trans {x} {y} {z} y≰x z≰y z≤x with ≤-dec y z
  ... | yes y≤z = y≰x (trans y≤z z≤x)
  ... | no  y≰z = either z≰y y≰z (z ≤|≥ y)

  ≰⇒> = id

  _<?_ : Decidable _≱_
  _<?_ x y with ≤-dec y x
  ... | yes y≤x = no λ y≰x → y≰x y≤x
  ... | no  y≰x = yes y≰x

fromPartialOrder : (po : PartialOrder A b) (_≤|≥_ : Total (PartialOrder._≤_ po)) → TotalOrder _ _ _
fromPartialOrder po tot = record { FromPartialOrder po tot }

module FromStrictPartialOrder {ℓ₁} {𝑆 : Type ℓ₁} {ℓ₂} (spo : StrictPartialOrder 𝑆 ℓ₂) (<-dec : Decidable (StrictPartialOrder._<_ spo)) where
  open StrictPartialOrder spo
  strictPartialOrder = spo
  _<?_ = <-dec

  partialOrder : PartialOrder _ _
  partialOrder .PartialOrder.preorder .Preorder._≤_ x y = ¬ (y < x)
  partialOrder .PartialOrder.preorder .Preorder.refl x<x = asym x<x x<x
  partialOrder .PartialOrder.preorder .Preorder.trans {x} {y} {z} y≮x z≮y z<x with x <? y
  ... | yes x<y = z≮y (trans z<x x<y)
  ... | no  x≮y = z≮y (subst (z <_) (conn x≮y y≮x) z<x)
  partialOrder .PartialOrder.antisym = flip conn

  ≰⇒> : ∀ {x y} → Stable (x < y)
  ≰⇒> {x} {y} = Dec→Stable (x < y) (x <? y)

  ≮⇒≥ = id

fromStrictPartialOrder : (spo : StrictPartialOrder A b) (_<?_ : Decidable (StrictPartialOrder._<_ spo)) → TotalOrder _ _ _
fromStrictPartialOrder spo _<?_ = record { FromStrictPartialOrder spo _<?_ }

record Equivalence {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  infix 4 _≋_
  field
    _≋_ : 𝑆 → 𝑆 → Type ℓ₂
    sym   : ∀ {x y} → x ≋ y → y ≋ x
    refl  : ∀ {x} → x ≋ x
    trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z

≡-equivalence : ∀ {a} {A : Type a} → Equivalence A a
≡-equivalence = record
  { _≋_ = _≡_
  ; sym = ≡.sym
  ; refl = ≡.refl
  ; trans = _;_
  }

