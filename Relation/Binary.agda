{-# OPTIONS --safe --cubical --postfix-projections #-}

module Relation.Binary where

open import Level
open import Relation.Nullary
open import Path as ≡ hiding (sym; refl)
open import Data.Sum
open import Function
open import Data.Bool as Bool using (Bool; true; false; T; bool)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Discrete
open import Data.Empty
open import Inspect

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

  infix 4 _≤ᵇ_ _≤?_

  _≤?_ : Decidable _≤_
  x ≤? y with y <? x
  ... | yes y<x = no (<⇒≱ y<x)
  ... | no  y≮x = yes (≮⇒≥ y≮x)

  _≤ᵇ_ : 𝑆 → 𝑆 → Bool
  x ≤ᵇ y = does (x ≤? y)

  _≤|≥_ : Total _≤_
  x ≤|≥ y with x <? y
  ... | yes x<y = inl (<⇒≤ x<y)
  ... | no  x≮y = inr (≮⇒≥ x≮y)

  open import Data.Unit
  open import Data.Empty
  open import Data.Sigma

  _≟_ : Discrete 𝑆
  x ≟ y with x <? y | y <? x
  ... | yes x<y | _ = no (λ x≡y → irrefl (subst (_< _) x≡y x<y))
  ... | _ | yes y<x = no (λ x≡y → irrefl (subst (_ <_) x≡y y<x))
  ... | no x≮y | no y≮x = yes (conn x≮y y≮x)

  data Ordering (x y : 𝑆) : Type (ℓ₁ ℓ⊔ ℓ₂) where
    lt : x < y → Ordering x y
    eq : x ≡ y → Ordering x y
    gt : x > y → Ordering x y

  compare : ∀ x y → Ordering x y
  compare x y with x <? y | y <? x
  ... | yes x<y | _ = lt x<y
  ... | no  x≮y | yes y<x = gt y<x
  ... | no  x≮y | no  y≮x = eq (conn x≮y y≮x)

  open import HLevels using (isSet)
  open import Relation.Nullary.Discrete.Properties using (Discrete→isSet)

  total⇒isSet : isSet 𝑆
  total⇒isSet = Discrete→isSet _≟_

  open import Data.Bool using (bool′)

  min-max : 𝑆 → 𝑆 → 𝑆 × 𝑆
  min-max x y = bool′ (y , x) (x , y) (x <ᵇ y)

  _⊔_ : 𝑆 → 𝑆 → 𝑆
  x ⊔ y = snd (min-max x y)

  _⊓_ : 𝑆 → 𝑆 → 𝑆
  x ⊓ y = fst (min-max x y)

  ⊓-assoc : ∀ x y z → (x ⊓ y) ⊓ z ≡ x ⊓ (y ⊓ z)
  ⊓-assoc x y z with x <? y | inspect (x <ᵇ_) y | y <? z | inspect (y <ᵇ_) z
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 with x <? z
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | yes x≤z = cong (fst ∘ bool _ _) (≡.sym xyp)
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | no  x≥z = ⊥-elim (x≥z (<-trans x≤y y≤z))
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 = cong (fst ∘ bool _ _) yzp ; cong (fst ∘ bool _ _) (≡.sym xyp)
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 = ≡.refl
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 with x <? z
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | yes x≤z = cong (fst ∘ bool _ _) yzp ; antisym (≤-trans (≮⇒≥ y≥z) (≮⇒≥ x≥y)) (<⇒≤ x≤z)
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | no x≥z = cong (fst ∘ bool _ _) yzp

  ⊔-assoc : ∀ x y z → (x ⊔ y) ⊔ z ≡ x ⊔ (y ⊔ z)
  ⊔-assoc x y z with x <? y | inspect (x <ᵇ_) y | y <? z | inspect (y <ᵇ_) z
  ⊔-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 with x <? z
  ⊔-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | yes x≤z = cong (snd ∘ bool _ _) yzp
  ⊔-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | no  x≥z = ⊥-elim (x≥z (<-trans x≤y y≤z))
  ⊔-assoc x y z | no  x≥y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 = ≡.refl
  ⊔-assoc x y z | yes x≤y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 = cong (snd ∘ bool _ _) yzp ; cong (snd ∘ bool _ _) (≡.sym xyp)
  ⊔-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 with x <? z
  ⊔-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | yes x≤z = antisym (≤-trans (≮⇒≥ y≥z) (≮⇒≥ x≥y)) (<⇒≤ x≤z) ; cong (snd ∘ bool _ _) (≡.sym xyp)
  ⊔-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | no x≥z = cong (snd ∘ bool _ _) (≡.sym xyp)

  min-max-comm : ∀ x y → min-max x y ≡ min-max y x
  min-max-comm x y with x <? y | inspect (x <ᵇ_) y | y <? x | inspect (y <ᵇ_) x
  min-max-comm x y | yes x<y | 〖 xy 〗 | yes y<x | 〖 yx 〗 = ⊥-elim (asym x<y y<x)
  min-max-comm x y | no  x≮y | 〖 xy 〗 | yes y<x | 〖 yx 〗 = ≡.refl
  min-max-comm x y | yes x<y | 〖 xy 〗 | no  y≮x | 〖 yx 〗 = ≡.refl
  min-max-comm x y | no  x≮y | 〖 xy 〗 | no  y≮x | 〖 yx 〗 = cong₂ _,_ (conn y≮x x≮y) (conn x≮y y≮x)

  ⊓-comm : ∀ x y → x ⊓ y ≡ y ⊓ x
  ⊓-comm x y = cong fst (min-max-comm x y)

  ⊔-comm : ∀ x y → x ⊔ y ≡ y ⊔ x
  ⊔-comm x y = cong snd (min-max-comm x y)

  min-max-idem : ∀ x → min-max x x ≡ (x , x)
  min-max-idem x = bool {P = λ r → bool′ (x , x) (x , x) r ≡ (x , x)} ≡.refl ≡.refl (x <ᵇ x)

  ⊓-idem : ∀ x → x ⊓ x ≡ x
  ⊓-idem x = cong fst (min-max-idem x)

  ⊔-idem : ∀ x → x ⊔ x ≡ x
  ⊔-idem x = cong snd (min-max-idem x)

module _ {ℓ₁} {𝑆 : Type ℓ₁} {ℓ₂} (partialOrder : PartialOrder 𝑆 ℓ₂) where
  open PartialOrder partialOrder
  open import Data.Sigma
  open import Relation.Nullary.Stable.Base

  open import Relation.Nullary.Decidable.Properties using (Dec→DoubleNegElim)
  open import Data.Unit

  module _ (_≤|≥_ : Total _≤_) where
    ≤-side : 𝑆 → 𝑆 → Bool
    ≤-side x y = is-l (x ≤|≥ y)

    ≤-dec : Decidable _≤_
    ≤-dec x y with x ≤|≥ y | y ≤|≥ x | inspect (≤-side x) y | inspect (≤-side y) x
    ≤-dec x y | inl x≤y | _       | _ | _ = yes x≤y
    ≤-dec x y | inr x≥y | inr y≥x | _ | _ = yes y≥x
    ≤-dec x y | inr x≥y | inl y≤x | 〖 x≥yᵇ 〗 | 〖 y≤xᵇ 〗 = no (x≢y ∘ flip antisym x≥y)
      where
      x≢y : x ≢ y
      x≢y x≡y = subst (bool ⊤ ⊥) (≡.sym x≥yᵇ ; cong₂ ≤-side x≡y (≡.sym x≡y) ; y≤xᵇ) tt

    ≤-stable : ∀ {x y} → Stable (x ≤ y)
    ≤-stable {x} {y} = Dec→DoubleNegElim _ (≤-dec x y)

    asym-≰ : Asymmetric _≰_
    asym-≰ {x} {y} x≰y y≰x = either x≰y y≰x (x ≤|≥ y)

    toStrict : StrictPartialOrder 𝑆 ℓ₂
    toStrict .StrictPartialOrder.strictPreorder .StrictPreorder._<_ x y = ¬ (y ≤ x)
    toStrict .StrictPartialOrder.conn x<y y<x = antisym (≤-stable y<x) (≤-stable x<y)
    toStrict .StrictPartialOrder.strictPreorder .StrictPreorder.irrefl y≰x = y≰x refl
    toStrict .StrictPartialOrder.strictPreorder .StrictPreorder.trans {x} {y} {z} y≰x z≰y z≤x with ≤-dec y z
    ... | yes y≤z = y≰x (trans y≤z z≤x)
    ... | no  y≰z = asym-≰ z≰y y≰z

    fromPartialOrder : TotalOrder 𝑆 ℓ₂ ℓ₂
    fromPartialOrder .TotalOrder.strictPartialOrder = toStrict
    fromPartialOrder .TotalOrder.partialOrder = partialOrder
    fromPartialOrder .TotalOrder.≰⇒> x≤y = x≤y
    fromPartialOrder .TotalOrder.≮⇒≥ = ≤-stable
    fromPartialOrder .TotalOrder._<?_ x y with ≤-dec y x
    ... | yes y≤x = no λ y≰x → y≰x y≤x
    ... | no  y≰x = yes y≰x

module _ {ℓ₁} {𝑆 : Type ℓ₁} {ℓ₂} (strictPartialOrder : StrictPartialOrder 𝑆 ℓ₂) where
  open StrictPartialOrder strictPartialOrder
  open import Data.Sigma
  open import Data.Sum
  open import Relation.Nullary.Decidable.Properties using (Dec→DoubleNegElim)

  module _ (_<?_ : Decidable _<_) where
    unStrict : PartialOrder 𝑆 _
    unStrict .PartialOrder.preorder .Preorder._≤_ x y = ¬ (y < x)
    unStrict .PartialOrder.preorder .Preorder.refl x<x = asym x<x x<x
    unStrict .PartialOrder.preorder .Preorder.trans {x} {y} {z} y≮x z≮y z<x with x <? y
    ... | yes x<y = z≮y (trans z<x x<y)
    ... | no  x≮y = z≮y (subst (z <_) (conn x≮y y≮x) z<x)
    unStrict .PartialOrder.antisym = flip conn

    fromStrictPartialOrder : TotalOrder 𝑆 _ _
    fromStrictPartialOrder .TotalOrder.strictPartialOrder = strictPartialOrder
    fromStrictPartialOrder .TotalOrder.partialOrder = unStrict
    fromStrictPartialOrder .TotalOrder.≰⇒> = Dec→DoubleNegElim _ (_ <? _)
    fromStrictPartialOrder .TotalOrder.≮⇒≥ = id
    fromStrictPartialOrder .TotalOrder._<?_ = _<?_

record Equivalence {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  infix 4 _≋_
  field
    _≋_ : 𝑆 → 𝑆 → Type ℓ₂
    sym   : ∀ {x y} → x ≋ y → y ≋ x
    refl  : ∀ {x} → x ≋ x
    trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z

≡-equivalence : ∀ {a} {A : Set a} → Equivalence A a
≡-equivalence = record
  { _≋_ = _≡_
  ; sym = ≡.sym
  ; refl = ≡.refl
  ; trans = _;_
  }

open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

trunc-equivalence : ∀ {a} {A : Type a} → Equivalence A a → Equivalence A a
trunc-equivalence e .Equivalence._≋_ x y = ∥ Equivalence._≋_ e x y ∥
trunc-equivalence e .Equivalence.sym = _∥$∥_ (Equivalence.sym e)
trunc-equivalence e .Equivalence.refl = ∣ Equivalence.refl e ∣
trunc-equivalence e .Equivalence.trans xy yz = ⦇ (Equivalence.trans e) xy yz ⦈
