{-# OPTIONS --safe --cubical #-}

module Relation.Binary where

open import Level
open import Relation.Nullary
open import Path as ≡ hiding (sym; refl)
open import Data.Sum
open import Function
open import Data.Bool as Bool using (Bool; true; false; T; bool)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Discrete

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

  Total : Type _
  Total = ∀ x y → (x ~ y) ⊎ (y ~ x)

data Tri {a r₁ r₂ r₃} {A : Type a} (R₁ : A → A → Type r₁) (R₂ : A → A → Type r₂) (R₃ : A → A → Type r₃) (x y : A) : Type (a ℓ⊔ r₁ ℓ⊔ r₂ ℓ⊔ r₃) where
  lt : (x<y : R₁ x y) → Tri R₁ R₂ R₃ x y
  eq : (x≡y : R₂ x y) → Tri R₁ R₂ R₃ x y
  gt : (x>y : R₃ x y) → Tri R₁ R₂ R₃ x y

record PartialOrder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  infix 4 _≤_
  field
    _≤_ : 𝑆 → 𝑆 → Type ℓ₂
    refl : Reflexive _≤_
    antisym : Antisymmetric _≤_
    trans : Transitive _≤_

record TotalOrder {ℓ₁} (𝑆 : Type ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  field
    partialOrder : PartialOrder 𝑆 ℓ₂
  open PartialOrder partialOrder public

  infix 4 _≤ᵇ_ _≤?_
  field
    _≤?_ : Total _≤_

  _≤ᵇ_ : 𝑆 → 𝑆 → Bool
  x ≤ᵇ y = is-l (x ≤? y)

  open import Data.Unit
  open import Data.Empty
  open import Data.Sigma

  total⇒discrete : Discrete 𝑆
  total⇒discrete x y with x ≤? y | inspect (x ≤?_) y | y ≤? x | inspect (y ≤?_) x
  total⇒discrete x y | inl x₁ | 〖 xy 〗 | inl x₂ | 〖 yx 〗 = yes (antisym x₁ x₂)
  total⇒discrete x y | inr x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = yes (antisym x₂ x₁)
  total⇒discrete x y | inl x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = no (λ p → subst (bool ⊥ ⊤) (cong is-l (≡.sym xy) ; cong₂ _≤ᵇ_ p (≡.sym p) ; cong is-l yx) tt)
  total⇒discrete x y | inr x₁ | 〖 xy 〗 | inl x₂ | 〖 yx 〗 = no (λ p → subst (bool ⊤ ⊥) (cong is-l (≡.sym xy) ; cong₂ _≤ᵇ_ p (≡.sym p) ; cong is-l yx) tt)


  infix 4 _<_
  _<_ : 𝑆 → 𝑆 → Type (ℓ₁ ℓ⊔ ℓ₂)
  x < y = (x ≢ y) × (x ≤ y)

  Ordering : 𝑆 → 𝑆 → Type (ℓ₁ ℓ⊔ ℓ₂)
  Ordering = Tri _<_ _≡_ (flip _<_)

  compare : ∀ x y → Ordering x y
  compare x y with x ≤? y | inspect (x ≤?_) y | y ≤? x | inspect (y ≤?_) x
  compare x y | inl x₁ | 〖 xy 〗 | inl x₂ | 〖 yx 〗 = eq (antisym x₁ x₂)
  compare x y | inr x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = eq (antisym x₂ x₁)
  compare x y | inl x₁ | 〖 xy 〗 | inr x₂ | 〖 yx 〗 = lt ((λ p → subst (bool ⊥ ⊤) (cong is-l (≡.sym xy) ; cong₂ _≤ᵇ_ p (≡.sym p) ; cong is-l yx) tt) , x₁)
  compare x y | inr x₁ | 〖 xy 〗 | inl x₂ | 〖 yx 〗 = gt ((λ p → subst (bool ⊤ ⊥) (cong is-l (≡.sym xy) ; cong₂ _≤ᵇ_ (≡.sym p) p ; cong is-l yx) tt) , x₁)

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
