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

data Ord : Type₀ where LT EQ GT : Ord

module _ {a r₁ r₂ r₃} {A : Type a} (R₁ : A → A → Type r₁) (R₂ : A → A → Type r₂) (R₃ : A → A → Type r₃) (x y : A) where
  data ProofOfOrder : Ord → Type (a ℓ⊔ r₁ ℓ⊔ r₂ ℓ⊔ r₃) where
    is-lt : R₁ x y → ProofOfOrder LT
    is-eq : R₂ x y → ProofOfOrder EQ
    is-gt : R₃ x y → ProofOfOrder GT

  record Tri : Type (a ℓ⊔ r₁ ℓ⊔ r₂ ℓ⊔ r₃) where
    constructor tri
    field
      ord : Ord
      proofOfOrder : ProofOfOrder ord
  open Tri public

pattern lt x = tri LT (is-lt x)
pattern eq x = tri EQ (is-eq x)
pattern gt x = tri GT (is-gt x)

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


  Ordering : 𝑆 → 𝑆 → Type (ℓ₁ ℓ⊔ ℓ₂)
  Ordering = Tri _<_ _≡_ (flip _<_)

  compare : ∀ x y → Ordering x y
  compare x y with x <? y
  compare x y | yes x<y = lt x<y
  compare x y | no  x≮y with y <? x
  compare x y | no  x≮y | yes y<x = gt y<x
  compare x y | no  x≮y | no  y≮x = eq (conn x≮y y≮x)

  <⇒≤ : ∀ {x y} → x < y → x ≤ y
  <⇒≤ = ≮⇒≥ ∘ asym

  _<ᵇ_ : 𝑆 → 𝑆 → Bool
  x <ᵇ y = does (x <? y)

  <⇒≱ : ∀ {x y} → x < y → x ≱ y
  <⇒≱ {x} {y} x<y = irrefl x<y ∘ antisym (<⇒≤ x<y)

  ≤⇒≯ : ∀ {x y} → x ≤ y → x ≯ y
  ≤⇒≯ {x} {y} x≤y x>y = irrefl x>y (antisym (≮⇒≥ (asym x>y)) x≤y)

  cmp : 𝑆 → 𝑆 → Ord
  cmp x y = ord (compare x y)

  infix 4 _≤ᵇ_ _≤?_

  _≤?_ : Decidable _≤_
  x ≤? y with y <? x
  x ≤? y | yes y<x = no (<⇒≱ y<x)
  x ≤? y | no  y≮x = yes (≮⇒≥ y≮x)

  _≤ᵇ_ : 𝑆 → 𝑆 → Bool
  x ≤ᵇ y = does (x ≤? y)

  _≤|≥_ : Total _≤_
  x ≤|≥ y with x <? y
  x ≤|≥ y | yes x<y = inl (<⇒≤ x<y)
  x ≤|≥ y | no  x≮y = inr (≮⇒≥ x≮y)

  open import Data.Unit
  open import Data.Empty
  open import Data.Sigma

  total⇒discrete : Discrete 𝑆
  total⇒discrete x y with compare x y
  ... | lt x<y = no (irrefl x<y)
  ... | eq x≡y = yes x≡y
  ... | gt x>y = no (irrefl x>y ∘ ≡.sym)


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


  open import Data.Unit

  module _ (_≤?_ : Total _≤_) where
    ≤-b : 𝑆 → 𝑆 → Bool
    ≤-b x y = is-l (x ≤? y)

    toStrict : StrictPartialOrder 𝑆 ℓ₂
    toStrict .StrictPartialOrder._<_ x y = ¬ (y ≤ x)
    toStrict .StrictPartialOrder.trans {x} {y} {z} y≰x z≰y z≤x = either (y≰x ∘ flip trans z≤x)  z≰y (y ≤? z)
    toStrict .StrictPartialOrder.asym {x} {y} y≰x x≰y = either x≰y y≰x (x ≤? y)
    toStrict .StrictPartialOrder.conn {x} {y} x<y y<x with x ≤? y | inspect (x ≤?_) y | y ≤? x | inspect (y ≤?_) x
    toStrict .StrictPartialOrder.conn {x} {y} x<y y<x | inl x₁ | xy | inl x₂ | yx = antisym x₁ x₂
    toStrict .StrictPartialOrder.conn {x} {y} x<y y<x | inl x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = ⊥-elim (x<y (x≢y ∘ antisym x₂))
      where
      x≢y : x ≢ y
      x≢y = (λ p → subst (bool ⊥ ⊤) (cong is-l (≡.sym xy) ; cong₂ ≤-b p (≡.sym p) ; cong is-l yx) tt)
    toStrict .StrictPartialOrder.conn {x} {y} x<y y<x | inr x₁ | 〖 xy 〗 | inl x₂ | 〖 yx 〗 = ⊥-elim (y<x (y≢x ∘ antisym x₂))
      where
      y≢x : y ≢ x
      y≢x = (λ p → subst (bool ⊤ ⊥) (cong is-l (≡.sym xy) ; cong₂ ≤-b (≡.sym p) p ; cong is-l yx) tt)
    toStrict .StrictPartialOrder.conn {x} {y} x<y y<x | inr x₁ | xy | inr x₂ | yx = antisym x₂ x₁

    fromPartialOrder : TotalOrder 𝑆 ℓ₂ ℓ₂
    fromPartialOrder .TotalOrder.strictPartialOrder = toStrict
    fromPartialOrder .TotalOrder.partialOrder = partialOrder
    fromPartialOrder .TotalOrder.≰⇒> x≤y = x≤y
    fromPartialOrder .TotalOrder.≮⇒≥ {x} {y} x<y with x ≤? y | inspect (x ≤?_) y | y ≤? x | inspect (y ≤?_) x
    fromPartialOrder .TotalOrder.≮⇒≥ {x} {y} x<y | inl x₁ | xy | inl x₂ | yx = x₂
    fromPartialOrder .TotalOrder.≮⇒≥ {x} {y} x<y | inl x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = ⊥-elim (x<y (x≢y ∘ antisym x₂))
      where
      x≢y : x ≢ y
      x≢y = (λ p → subst (bool ⊥ ⊤) (cong is-l (≡.sym xy) ; cong₂ ≤-b p (≡.sym p) ; cong is-l yx) tt)
    fromPartialOrder .TotalOrder.≮⇒≥ {x} {y} x<y | inr x₁ | xy | inl x₂ | yx = x₂
    fromPartialOrder .TotalOrder.≮⇒≥ {x} {y} x<y | inr x₁ | xy | inr x₂ | yx = x₁
    fromPartialOrder .TotalOrder._<?_ x y with x ≤? y | inspect (x ≤?_) y
    fromPartialOrder .TotalOrder._<?_ x y | inr y≤x | _ = no λ y≰x → y≰x y≤x
    fromPartialOrder .TotalOrder._<?_ x y | inl x≤y | _ with y ≤? x | inspect (y ≤?_) x
    fromPartialOrder .TotalOrder._<?_ x y | inl x≤y | _ | inl y≤x | _ = no (λ y≰x → y≰x y≤x)
    fromPartialOrder .TotalOrder._<?_ x y | inl x≤y | 〖 xy 〗 | inr y≥x | 〖 yx 〗 = yes λ y≤x → x≢y (antisym x≤y y≤x)
      where
      x≢y : x ≢ y
      x≢y p = subst (bool ⊥ ⊤) (cong is-l (≡.sym xy) ; cong₂ ≤-b p (≡.sym p) ; cong is-l yx) tt

module _ {ℓ₁} {𝑆 : Type ℓ₁} {ℓ₂} (strictPartialOrder : StrictPartialOrder 𝑆 ℓ₂) where
  open StrictPartialOrder strictPartialOrder
  open import Data.Sigma
  open import Data.Sum
  open import Relation.Nullary.Decidable.Properties using (Dec→DoubleNegElim)

  module _ (_<?_ : Decidable _<_) where

    lt-or-eq : ∀ {x y} → ¬ (x < y) → (y < x) ⊎ (x ≡ y)
    lt-or-eq {x} {y} x≮y with y <? x
    lt-or-eq {x} {y} x≮y | no  why₁ = inr (conn x≮y why₁)
    lt-or-eq {x} {y} x≮y | yes why₁ = inl why₁

    unStrict : PartialOrder 𝑆 _
    unStrict .PartialOrder._≤_ x y = ¬ (y < x)
    unStrict .PartialOrder.refl x<x = asym x<x x<x
    unStrict .PartialOrder.antisym = flip conn
    unStrict .PartialOrder.trans {x} {y} {z} y≮x z≮y z<x with lt-or-eq y≮x | lt-or-eq z≮y
    unStrict .PartialOrder.trans {x} {y} {z} y≮x z≮y z<x | inl x₁ | inl x₂ = z≮y (trans z<x x₁)
    unStrict .PartialOrder.trans {x} {y} {z} y≮x z≮y z<x | inl x₁ | inr x₂ = z≮y (trans z<x x₁)
    unStrict .PartialOrder.trans {x} {y} {z} y≮x z≮y z<x | inr x₁ | inl x₂ = y≮x (trans x₂ z<x)
    unStrict .PartialOrder.trans {x} {y} {z} y≮x z≮y z<x | inr x₁ | inr x₂ = z≮y (subst (z <_) (≡.sym x₁) z<x)

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
