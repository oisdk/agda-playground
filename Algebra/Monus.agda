{-# OPTIONS --cubical --safe #-}

module Algebra.Monus where

open import Prelude
open import Algebra
open import Relation.Binary
open import Path.Reasoning

-- Positively ordered monoids
record POM ℓ : Type (ℓsuc ℓ) where
  field commutativeMonoid : CommutativeMonoid ℓ
  open CommutativeMonoid commutativeMonoid public
  field preorder : Preorder 𝑆 ℓ
  open Preorder preorder public
  field
    positive : ∀ {x} → ε ≤ x
    ≤-cong : ∀ {x y} z → x ≤ y → x ∙ z ≤ y ∙ z

  algebraic : ∀ {x y} → x ≤ y ∙ x
  algebraic {x} {y} = subst (_≤ y ∙ x) (ε∙ x) (≤-cong x (positive {x = y}))

-- Commutative Monoids with Monus
record CMM ℓ : Type (ℓsuc ℓ) where
  field commutativeMonoid : CommutativeMonoid ℓ
  open CommutativeMonoid commutativeMonoid public

  field _∸_ : 𝑆 → 𝑆 → 𝑆
  infixl 6 _∸_
  field
    ∸‿comm  : ∀ x y → x ∙ (y ∸ x) ≡ y ∙ (x ∸ y)
    ∸‿assoc : ∀ x y z → (x ∸ y) ∸ z ≡ x ∸ (y ∙ z)
    ∸‿inv   : ∀ x → x ∸ x ≡ ε
    ε∸      : ∀ x → ε ∸ x ≡ ε

  open import Path.Reasoning

  ∸ε : ∀ x → x ∸ ε ≡ x
  ∸ε x =
    x ∸ ε ≡˘⟨ ε∙ (x ∸ ε) ⟩
    ε ∙ (x ∸ ε) ≡⟨ ∸‿comm ε x ⟩
    x ∙ (ε ∸ x) ≡⟨ cong (x ∙_) (ε∸ x) ⟩
    x ∙ ε ≡⟨ ∙ε x ⟩
    x ∎

-- Cancellative Commutative Monoids with Monus
record CCMM ℓ : Type (ℓsuc ℓ) where
  field cmm : CMM ℓ
  open CMM cmm public

  field ∸‿cancel : ∀ x y → (x ∙ y) ∸ x ≡ y

  open import Path.Reasoning

  cancelˡ : Cancellativeˡ _∙_
  cancelˡ x y z p =
    y ≡˘⟨ ∸‿cancel x y ⟩
    (x ∙ y) ∸ x ≡⟨ cong (_∸ x) p ⟩
    (x ∙ z) ∸ x ≡⟨ ∸‿cancel x z ⟩
    z ∎

  cancelʳ : Cancellativeʳ _∙_
  cancelʳ x y z p =
    y ≡˘⟨ ∸‿cancel x y ⟩
    (x ∙ y) ∸ x ≡⟨ cong (_∸ x) (comm x y) ⟩
    (y ∙ x) ∸ x ≡⟨ cong (_∸ x) p ⟩
    (z ∙ x) ∸ x ≡⟨ cong (_∸ x) (comm z x) ⟩
    (x ∙ z) ∸ x ≡⟨ ∸‿cancel x z ⟩
    z ∎


record Monus ℓ : Type (ℓsuc ℓ) where
  field
    commutativeMonoid : CommutativeMonoid ℓ
  open CommutativeMonoid commutativeMonoid public
  infix 4 _≤_
  _≤_ : 𝑆 → 𝑆 → Type ℓ
  x ≤ y = ∃[ z ] (y ≡ x ∙ z)
  field
    _≤|≥_ : Total _≤_
    antisym : Antisymmetric _≤_

  ≤-refl : Reflexive _≤_
  ≤-refl = ε , sym (∙ε _)

  ≤-trans : Transitive _≤_
  ≤-trans (k₁ , _) (k₂ , _) .fst = k₁ ∙ k₂
  ≤-trans {x} {y} {z} (k₁ , y≡x∙k₁) (k₂ , z≡y∙k₂) .snd =
    z ≡⟨ z≡y∙k₂ ⟩
    y ∙ k₂ ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
    (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
    x ∙ (k₁ ∙ k₂) ∎

  positive : ∀ x → ε ≤ x
  positive x = x , sym (ε∙ x)

  ∙-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z
  ∙-cong x (k , z≡y∙k) = k , cong (x ∙_) z≡y∙k ; sym (assoc x _ k)

  ∙-congʳ : ∀ x {y z} → y ≤ z → y ∙ x ≤ z ∙ x
  ∙-congʳ x {y} {z} p = subst (y ∙ x ≤_) (comm x z) (subst (_≤ x ∙ z) (comm x y) (∙-cong x p))

  zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
  zeroSumFree x y x∙y≡ε = antisym (y , sym x∙y≡ε) (positive x)

  partialOrder : PartialOrder 𝑆 ℓ
  Preorder._≤_   (PartialOrder.preorder partialOrder) = _≤_
  Preorder.refl  (PartialOrder.preorder partialOrder) = ≤-refl
  Preorder.trans (PartialOrder.preorder partialOrder) = ≤-trans
  PartialOrder.antisym partialOrder = antisym

  totalOrder : TotalOrder 𝑆 ℓ ℓ
  totalOrder = fromPartialOrder partialOrder _≤|≥_

  open TotalOrder totalOrder
    hiding (refl; antisym; _≤_; _≤|≥_; partialOrder; ≤-trans)
    public

  diff≢ε : ∀ {x y} → (x<y : x < y) → fst (<⇒≤ x<y) ≢ ε
  diff≢ε x<y with <⇒≤ x<y
  diff≢ε x<y | k , y≡x∙k = λ k≡ε → irrefl (subst (_< _) (sym (y≡x∙k ; cong (_ ∙_) k≡ε ; ∙ε _)) x<y)
