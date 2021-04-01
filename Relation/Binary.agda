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
  Irreflexive = ∀ {x y} → x ~ y → x ≢ y

  Total : Type _
  Total = ∀ x y → (x ~ y) ⊎ (y ~ x)

record StrictPartialOrder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  infix 4 _<_
  field
    _<_ : 𝑆 → 𝑆 → Type ℓ₂
    trans : Transitive _<_
    asym : Asymmetric _<_
    conn : Connected _<_

  irrefl : Irreflexive _<_
  irrefl {x} {y} x<y x≡y = asym x<y (subst  (y <_) (≡.sym x≡y) (subst (_< y) x≡y x<y))

  infix 4 _≮_ _>_ _≯_
  _≮_ _>_ _≯_ : 𝑆 → 𝑆 → Type ℓ₂
  x ≮ y = ¬ (x < y)
  x > y = y < x
  x ≯ y = ¬ (y < x)

record PartialOrder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  infix 4 _≤_
  field
    _≤_ : 𝑆 → 𝑆 → Type ℓ₂
    refl : Reflexive _≤_
    antisym : Antisymmetric _≤_
    trans : Transitive _≤_

  infix 4 _≰_ _≥_ _≱_
  _≰_ _≥_ _≱_ : 𝑆 → 𝑆 → Type ℓ₂
  x ≰ y = ¬ (x ≤ y)
  x ≥ y = y ≤ x
  x ≱ y = ¬ (y ≤ x)

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
  <⇒≱ {x} {y} x<y = irrefl x<y ∘ antisym (<⇒≤ x<y)

  ≤⇒≯ : ∀ {x y} → x ≤ y → x ≯ y
  ≤⇒≯ {x} {y} x≤y x>y = irrefl x>y (antisym (≮⇒≥ (asym x>y)) x≤y)

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
  ... | yes x<y | _ = no (irrefl x<y)
  ... | _ | yes y<x = no (irrefl y<x ∘ ≡.sym)
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

  _⊔_ : 𝑆 → 𝑆 → 𝑆
  x ⊔ y = bool′ x y (x <ᵇ y)

  _⊓_ : 𝑆 → 𝑆 → 𝑆
  x ⊓ y = bool′ y x (x <ᵇ y)

  ⊓-assoc : ∀ x y z → (x ⊓ y) ⊓ z ≡ x ⊓ (y ⊓ z)
  ⊓-assoc x y z with x <? y | inspect (x <ᵇ_) y | y <? z | inspect (y <ᵇ_) z
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 with x <? z
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | yes x≤z = cong (bool y x) (≡.sym xyp)
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | no  x≥z = ⊥-elim (x≥z (<-trans x≤y y≤z))
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 = cong (bool z y) yzp ; cong (bool y x) (≡.sym xyp)
  ⊓-assoc x y z | yes x≤y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 = ≡.refl
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 with x <? z
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | yes x≤z = cong (bool z y) yzp ; antisym (≤-trans (≮⇒≥ y≥z) (≮⇒≥ x≥y)) (<⇒≤ x≤z)
  ⊓-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | no x≥z = cong (bool z y) yzp

  ⊓-comm : ∀ x y → x ⊓ y ≡ y ⊓ x
  ⊓-comm x y with x <? y | inspect (x <ᵇ_) y | y <? x | inspect (y <ᵇ_) x
  ⊓-comm x y | yes x₁ | 〖 xyp 〗 | yes x₂ | 〖 yxp 〗 = ⊥-elim (asym x₁ x₂)
  ⊓-comm x y | no  x₁ | 〖 xyp 〗 | yes x₂ | 〖 yxp 〗 = ≡.refl
  ⊓-comm x y | yes x₁ | 〖 xyp 〗 | no  x₂ | 〖 yxp 〗 = ≡.refl
  ⊓-comm x y | no  x₁ | 〖 xyp 〗 | no  x₂ | 〖 yxp 〗 = conn x₂ x₁

module _ {ℓ₁} {𝑆 : Type ℓ₁} {ℓ₂} (partialOrder : PartialOrder 𝑆 ℓ₂) where
  open PartialOrder partialOrder
  open import Data.Sigma
  open import Relation.Nullary.Stable.Base

  open import Data.Unit

  module FromDec (_≤?_ : Decidable _≤_) (asym : ∀ {x y} → x ≰ y → y ≰ x → ⊥) where
    ≤-stable : ∀ {x y} → Stable (x ≤ y)
    ≤-stable {x} {y} ¬¬x≤y with x ≤? y
    ... | yes x≤y = x≤y
    ... | no  x≰y = ⊥-elim (¬¬x≤y x≰y)

    toStrict : StrictPartialOrder 𝑆 ℓ₂
    toStrict .StrictPartialOrder._<_ x y = ¬ (y ≤ x)
    toStrict .StrictPartialOrder.conn x<y y<x = antisym (≤-stable y<x) (≤-stable x<y)
    toStrict .StrictPartialOrder.asym = asym
    toStrict .StrictPartialOrder.trans {x} {y} {z} y≰x z≰y z≤x with y ≤? z
    ... | yes y≤z = y≰x (trans y≤z z≤x)
    ... | no  y≰z = asym z≰y y≰z

    fromPartialOrder : TotalOrder 𝑆 ℓ₂ ℓ₂
    fromPartialOrder .TotalOrder.strictPartialOrder = toStrict
    fromPartialOrder .TotalOrder.partialOrder = partialOrder
    fromPartialOrder .TotalOrder.≰⇒> x≤y = x≤y
    fromPartialOrder .TotalOrder.≮⇒≥ = ≤-stable
    fromPartialOrder .TotalOrder._<?_ x y with y ≤? x
    ... | yes y≤x = no λ y≰x → y≰x y≤x
    ... | no  y≰x = yes y≰x

  module _ (_≤?_ : Total _≤_) where
    ≤-dec : Decidable _≤_
    ≤-dec x y with x ≤? y | inspect (x ≤?_) y
    ≤-dec x y | inl x≤y | _ = yes x≤y
    ≤-dec x y | inr x≥y | _ with y ≤? x | inspect (y ≤?_) x
    ≤-dec x y | inr x≥y | _ | inr y≥x | _ = yes y≥x
    ≤-dec x y | inr x≥y | 〖 pxy 〗 | inl y≤x | 〖 pyx 〗 = no λ x≤y → x≢y (antisym x≤y x≥y)
      where
      ≤-b : 𝑆 → 𝑆 → Bool
      ≤-b x y = is-l (x ≤? y)

      x≢y : x ≢ y
      x≢y p = subst (bool ⊤ ⊥) (cong is-l (≡.sym pxy) ; cong₂ ≤-b p (≡.sym p) ; cong is-l pyx) tt

    asym-≰ : Asymmetric _≰_
    asym-≰ {x} {y} x≰y y≰x = either x≰y y≰x (x ≤? y)

    open FromDec ≤-dec asym-≰ public using (fromPartialOrder)

module _ {ℓ₁} {𝑆 : Type ℓ₁} {ℓ₂} (strictPartialOrder : StrictPartialOrder 𝑆 ℓ₂) where
  open StrictPartialOrder strictPartialOrder
  open import Data.Sigma
  open import Data.Sum
  open import Relation.Nullary.Decidable.Properties using (Dec→DoubleNegElim)

  module _ (_<?_ : Decidable _<_) where
    unStrict : PartialOrder 𝑆 _
    unStrict .PartialOrder._≤_ x y = ¬ (y < x)
    unStrict .PartialOrder.refl x<x = asym x<x x<x
    unStrict .PartialOrder.antisym = flip conn
    unStrict .PartialOrder.trans {x} {y} {z} y≮x z≮y z<x with x <? y
    ... | yes x<y = z≮y (trans z<x x<y)
    ... | no  x≮y = z≮y (subst (z <_) (conn x≮y y≮x) z<x)

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
