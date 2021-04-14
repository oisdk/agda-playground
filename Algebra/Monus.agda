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
    positive : ∀ x → ε ≤ x
    ≤-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z

  x≤x∙y : ∀ {x y} → x ≤ x ∙ y
  x≤x∙y {x} {y} = subst (_≤ x ∙ y) (∙ε x) (≤-cong x (positive y))

  ≤-congʳ : ∀ x {y z} → y ≤ z → y ∙ x ≤ z ∙ x
  ≤-congʳ x {y} {z} p = subst (y ∙ x ≤_) (comm x z) (subst (_≤ x ∙ z) (comm x y) (≤-cong x p))

-- Every commutative monoid generates a positively ordered monoid
-- called the "algebraic" pom
module AlgebraicPOM {ℓ} (mon : CommutativeMonoid ℓ) where
  commutativeMonoid = mon
  open CommutativeMonoid mon

  infix 4 _≤_
  _≤_ : 𝑆 → 𝑆 → Type _
  x ≤ y = ∃[ z ] (y ≡ x ∙ z)

  ≤-trans : Transitive _≤_
  ≤-trans (k₁ , _) (k₂ , _) .fst = k₁ ∙ k₂
  ≤-trans {x} {y} {z} (k₁ , y≡x∙k₁) (k₂ , z≡y∙k₂) .snd =
    z ≡⟨ z≡y∙k₂ ⟩
    y ∙ k₂ ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
    (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
    x ∙ (k₁ ∙ k₂) ∎

  preorder : Preorder 𝑆 ℓ
  Preorder._≤_ preorder = _≤_
  Preorder.refl preorder = ε , sym (∙ε _)
  Preorder.trans preorder = ≤-trans

  positive : ∀ x → ε ≤ x
  positive x = x , sym (ε∙ x)

  ≤-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z
  ≤-cong x (k , z≡y∙k) = k , cong (x ∙_) z≡y∙k ; sym (assoc x _ k)

algebraic-pom : ∀ {ℓ} → CommutativeMonoid ℓ → POM ℓ
algebraic-pom mon = record { AlgebraicPOM mon }

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

  pom : POM _
  pom = algebraic-pom commutativeMonoid

  open POM pom public hiding (semigroup; commutativeMonoid; monoid; _∙_; ε; assoc; comm; ε∙; ∙ε)

  zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
  zeroSumFree x y x∙y≡ε = sym (∸‿cancel y x) ; cong (_∸ y) (comm y x ; x∙y≡ε) ; ε∸ y

  antisym : Antisymmetric _≤_
  antisym {x} {y} (k₁ , y≡x∙k₁) (k₂ , x≡y∙k₂) =
    sym (y≡x∙k₁ ; cong (x ∙_) (zeroSumFree k₁ k₂ (sym (sym (∸‿inv x) ; cong (_∸ x) (x≡y∙k₂ ; cong (_∙ k₂) y≡x∙k₁ ; assoc x k₁ k₂) ; ∸‿cancel x (k₁ ∙ k₂)))) ; ∙ε x)

  partialOrder : PartialOrder _ _
  PartialOrder.preorder partialOrder = preorder
  PartialOrder.antisym partialOrder = antisym

record TMPOM ℓ : Type (ℓsuc ℓ) where
  field commutativeMonoid : CommutativeMonoid ℓ

  pom : POM _
  pom = algebraic-pom commutativeMonoid

  open POM pom public hiding (refl)

  field
    _≤|≥_ : Total _≤_
    antisym : Antisymmetric _≤_

  zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
  zeroSumFree x y x∙y≡ε = antisym (y , sym x∙y≡ε) (positive x)

  totalOrder : TotalOrder 𝑆 ℓ ℓ
  totalOrder = fromPartialOrder (record { preorder = preorder ; antisym = antisym }) _≤|≥_

  open TotalOrder totalOrder
    hiding (refl; antisym; _≤_; _≤|≥_; partialOrder; ≤-trans; _≥_; _≰_; _≱_)
    public

  diff≢ε : ∀ {x y} → (x<y : x < y) → fst (<⇒≤ x<y) ≢ ε
  diff≢ε x<y with <⇒≤ x<y
  diff≢ε x<y | k , y≡x∙k = λ k≡ε → irrefl (subst (_< _) (sym (y≡x∙k ; cong (_ ∙_) k≡ε ; ∙ε _)) x<y)

  -- module ToCMM where
  --   _∸_ : 𝑆 → 𝑆 → 𝑆
  --   x ∸ y with compare x y
  --   (x ∸ y) | lt x<y = ε
  --   (x ∸ y) | eq x≡y = ε
  --   (x ∸ y) | gt x>y = fst (<⇒≤ x>y)

  --   ∸‿≤ : ∀ x y → x ≤ y → x ∸ y ≡ ε
  --   ∸‿≤ x y x≤y with compare x y
  --   ∸‿≤ x y x≤y | lt _ = refl
  --   ∸‿≤ x y x≤y | eq _ = refl
  --   ∸‿≤ x y x≤y | gt x>y = ⊥-elim (x>y x≤y)

  --   ∸‿inv : ∀ x → x ∸ x ≡ ε
  --   ∸‿inv x with compare x x
  --   ∸‿inv x | lt x<x = ⊥-elim (irrefl x<x)
  --   ∸‿inv x | eq x≡x = refl
  --   ∸‿inv x | gt x>x = ⊥-elim (irrefl x>x)

  --   ε∸ : ∀ x → ε ∸ x ≡ ε
  --   ε∸ x with compare ε x
  --   ε∸ x | lt ε<x = refl
  --   ε∸ x | eq ε≡x = refl
  --   ε∸ x | gt ε>x = ⊥-elim (<⇒≱ ε>x (positive x))

  --   ∸‿comm : ∀ x y → x ∙ (y ∸ x) ≡ y ∙ (x ∸ y)
  --   ∸‿comm x y with compare y x | compare x y
  --   ∸‿comm x y | lt y<x | lt x<y = ⊥-elim (asym x<y y<x)
  --   ∸‿comm x y | gt y>x | gt x>y = ⊥-elim (asym x>y y>x)
  --   ∸‿comm x y | gt y>x | eq x≡y = ⊥-elim (irrefl (subst (_< y) x≡y y>x))
  --   ∸‿comm x y | eq y≡x | gt x>y = ⊥-elim (irrefl (subst (_< x) y≡x x>y))
  --   ∸‿comm x y | eq y≡x | lt x<y = ⊥-elim (irrefl (subst (x <_) y≡x x<y))
  --   ∸‿comm x y | lt y<x | eq x≡y = ⊥-elim (irrefl (subst (y <_) x≡y y<x))
  --   ∸‿comm x y | eq y≡x | eq x≡y = cong (_∙ ε) x≡y
  --   ∸‿comm x y | gt y>x | lt x<y = sym (snd (<⇒≤ y>x)) ; sym (∙ε y)
  --   ∸‿comm x y | lt y<x | gt x>y = ∙ε x ; snd (<⇒≤ x>y)

  --   ∸‿assoc : ∀ x y z → (x ∸ y) ∸ z ≡ x ∸ (y ∙ z)
  --   ∸‿assoc x y z with compare x y
  --   ∸‿assoc x y z | lt x<y = ε∸ z ; sym (∸‿≤ x (y ∙ z) (trans (<⇒≤ x<y) x≤x∙y))
  --   ∸‿assoc x y z | eq x≡y = ε∸ z ; sym (∸‿≤ x (y ∙ z) (subst (_≤ y ∙ z) (sym x≡y) x≤x∙y))
  --   ∸‿assoc x y z | gt x>y with <⇒≤ x>y | compare x (y ∙ z)
  --   ∸‿assoc x y z | gt x>y | k , x≡y∙k | lt x<y∙z = k ∸ z ≡⟨ {!!} ⟩ ε ∎
  --   ∸‿assoc x y z | gt x>y | k , x≡y∙k | eq x≡y∙z = k ∸ z ≡⟨ {!!} ⟩ ε ∎
  --   ∸‿assoc x y z | gt x>y | k , x≡y∙k | gt x>y∙z with <⇒≤ x>y∙z
  --   ∸‿assoc x y z | gt x>y | k₁ , x≡y∙k₁ | gt x>y∙z | k₂ , x≡y∙z∙k₁∙k₂ = k₁ ∸ z ≡⟨ {!!} ⟩ k₂ ∎

