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

data Tri {a r₁ r₂ r₃} {A : Type a} (R₁ : A → A → Type r₁) (R₂ : A → A → Type r₂) (R₃ : A → A → Type r₃) (x y : A) : Type (a ℓ⊔ r₁ ℓ⊔ r₂ ℓ⊔ r₃) where
  lt : (x<y : R₁ x y) → Tri R₁ R₂ R₃ x y
  eq : (x≡y : R₂ x y) → Tri R₁ R₂ R₃ x y
  gt : (x>y : R₃ x y) → Tri R₁ R₂ R₃ x y

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

data Ord : Type₀ where LT EQ GT : Ord
ord : ∀ {a r₁ r₂ r₃} {A : Type a} {R₁ : A → A → Type r₁} {R₂ : A → A → Type r₂} {R₃ : A → A → Type r₃} {x y : A} →
      Tri R₁ R₂ R₃ x y → Ord
ord (lt x<y) = LT
ord (eq x≡y) = EQ
ord (gt x>y) = GT

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

  Ordering : 𝑆 → 𝑆 → Type (ℓ₁ ℓ⊔ ℓ₂)
  Ordering = Tri _<_ _≡_ (flip _<_)

  field
    compare : ∀ x y → Ordering x y

    ≰⇒> : ∀ {x y} → x ≰ y → x > y
    ≮⇒≥ : ∀ {x y} → x ≮ y → x ≥ y

  infix 4 _<?_
  _<?_ : Decidable _<_
  x <? y with compare x y
  (x <? y) | lt x<y = yes x<y
  (x <? y) | eq x≡y = no λ x<y → irrefl x<y x≡y
  (x <? y) | gt x>y = no (asym x>y)

  _<ᵇ_ : 𝑆 → 𝑆 → Bool
  x <ᵇ y = does (x <? y)

  <⇒≱ : ∀ {x y} → x < y → x ≱ y
  <⇒≱ {x} {y} x<y = irrefl x<y ∘ antisym (≮⇒≥ (asym x<y))

  ≤⇒≯ : ∀ {x y} → x ≤ y → x ≯ y
  ≤⇒≯ {x} {y} x≤y x>y = irrefl x>y (antisym (≮⇒≥ (asym x>y)) x≤y)

  cmp : 𝑆 → 𝑆 → Ord
  cmp x y = ord (compare x y)

  infix 4 _≤ᵇ_ _≤?_

  _≤?_ : Decidable _≤_
  x ≤? y with compare x y
  (x ≤? y) | lt x<y = yes (≮⇒≥ (asym x<y))
  (x ≤? y) | eq x≡y = yes (subst (x ≤_) x≡y refl)
  (x ≤? y) | gt x>y = no (<⇒≱ x>y)


  _≤ᵇ_ : 𝑆 → 𝑆 → Bool
  x ≤ᵇ y = does (x ≤? y)

  ≤-total : Total _≤_
  ≤-total x y with compare x y
  ≤-total x y | lt x<y = inl (≮⇒≥ (asym x<y))
  ≤-total x y | eq x≡y = inl (subst (x ≤_) x≡y refl)
  ≤-total x y | gt x>y = inr (≮⇒≥ (asym x>y))

  open import Data.Unit
  open import Data.Empty
  open import Data.Sigma

  total⇒discrete : Discrete 𝑆
  total⇒discrete x y with compare x y
  ... | lt x<y = no (irrefl x<y)
  ... | eq x≡y = yes x≡y
  ... | gt x>y = no (irrefl x>y ∘ ≡.sym)

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
    fromPartialOrder .TotalOrder.compare x y with x ≤? y | inspect (x ≤?_) y | y ≤? x | inspect (y ≤?_) x
    fromPartialOrder .TotalOrder.compare x y | inl x₁ | 〖 xy 〗 | inl x₂ | 〖 yx 〗 = eq (antisym x₁ x₂)
    fromPartialOrder .TotalOrder.compare x y | inr x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = eq (antisym x₂ x₁)
    fromPartialOrder .TotalOrder.compare x y | inl x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = lt (λ y≤x → subst (bool ⊥ ⊤) (cong is-l (≡.sym xy) ; cong₂ ≤-b (antisym x₂ y≤x) (≡.sym (antisym x₂ y≤x)) ; cong is-l yx) tt)
    fromPartialOrder .TotalOrder.compare x y | inr x₁ | 〖 xy 〗 | inl x₂ | 〖 yx 〗 = gt (λ x≤y → subst (bool ⊤ ⊥) (cong is-l (≡.sym xy) ; cong₂ ≤-b (≡.sym (antisym x₂ x≤y)) (antisym x₂ x≤y) ; cong is-l yx) tt)

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
    fromStrictPartialOrder .TotalOrder.compare x y with x <? y
    fromStrictPartialOrder .TotalOrder.compare x y | yes why₁ = lt why₁
    fromStrictPartialOrder .TotalOrder.compare x y | no why₁ with lt-or-eq why₁
    fromStrictPartialOrder .TotalOrder.compare x y | no why₁ | inl x₁ = gt x₁
    fromStrictPartialOrder .TotalOrder.compare x y | no why₁ | inr x₁ = eq x₁

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
