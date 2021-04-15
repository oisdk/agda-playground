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

  infix 4 _≤|≥_
  field _≤|≥_ : Total _≤_

-- Total Minimal Antisymmetric POM
record TMAPOM ℓ : Type (ℓsuc ℓ) where
  field tmpom : TMPOM ℓ
  open TMPOM tmpom public
  field antisym : Antisymmetric _≤_

  zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
  zeroSumFree x y x∙y≡ε = antisym (y , sym x∙y≡ε) (positive x)

  totalOrder : TotalOrder 𝑆 ℓ ℓ
  totalOrder = fromPartialOrder (record { preorder = preorder ; antisym = antisym }) _≤|≥_


  module Viterbi where
    open import Relation.Binary.Construct.UpperBound totalOrder
    open TotalOrder ub-ord hiding (refl)
    open import Relation.Binary.Lattice ub-ord

    module NS where

      _*_ : ⌈∙⌉ → ⌈∙⌉ → ⌈∙⌉
      ⌈⊤⌉  *  y = ⌈⊤⌉
      ⌈ x ⌉ * ⌈⊤⌉ = ⌈⊤⌉
      ⌈ x ⌉ * ⌈ y ⌉ = ⌈ x ∙ y ⌉

      *-assoc : Associative _*_
      *-assoc ⌈⊤⌉ ⌈⊤⌉ ⌈⊤⌉ = refl
      *-assoc ⌈⊤⌉ ⌈⊤⌉ ⌈ x ⌉ = refl
      *-assoc ⌈⊤⌉ ⌈ x ⌉ ⌈⊤⌉ = refl
      *-assoc ⌈⊤⌉ ⌈ x ⌉ ⌈ x₁ ⌉ = refl
      *-assoc ⌈ x ⌉ ⌈⊤⌉ ⌈⊤⌉ = refl
      *-assoc ⌈ x ⌉ ⌈⊤⌉ ⌈ x₁ ⌉ = refl
      *-assoc ⌈ x ⌉ ⌈ x₁ ⌉ ⌈⊤⌉ = refl
      *-assoc ⌈ x ⌉ ⌈ x₁ ⌉ ⌈ x₂ ⌉ = cong ⌈_⌉ (assoc x x₁ x₂)

      *-com : Commutative _*_
      *-com ⌈⊤⌉   ⌈⊤⌉ = refl
      *-com ⌈⊤⌉   ⌈ x ⌉ = refl
      *-com ⌈ x ⌉ ⌈⊤⌉ = refl
      *-com ⌈ x ⌉ ⌈ y ⌉ = cong ⌈_⌉ (comm x y)

      ⟨+⟩* : _*_ Distributesˡ _⊓_
      ⟨+⟩* ⌈⊤⌉ _ _ = refl
      ⟨+⟩* ⌈ x ⌉ ⌈⊤⌉ ⌈⊤⌉ = refl
      ⟨+⟩* ⌈ x ⌉ ⌈⊤⌉ ⌈ z ⌉ = refl
      ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈⊤⌉ = *-com _ _
      ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ with ⌈ x ⌉ <? ⌈ y ⌉ | ⌈ x ∙ z ⌉ <? ⌈ y ∙ z ⌉
      ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | yes x<y | yes xz<yz = refl
      ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | no  x≮y | no  xz≮yz = refl
      ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | no  x≮y | yes xz<yz = ⊥-elim (xz<yz (≤-congʳ z (≮⇒≥ x≮y)))
      ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | yes x<y | no  xz≮yz = TotalOrder.antisym ub-ord (≤-congʳ z (<⇒≤ x<y)) (≮⇒≥ xz≮yz)

      𝑅 = ⌈∙⌉

      _+_ = _⊓_

      1# = ⌈ ε ⌉
      0# = ⌈⊤⌉

      +-assoc = ⊓-assoc

      0+ : ∀ x → ⌈⊤⌉ ⊓ x ≡ x
      0+ ⌈ x ⌉ = refl
      0+ ⌈⊤⌉ = refl

      +0 : ∀ x → x ⊓ ⌈⊤⌉ ≡ x
      +0 ⌈ x ⌉ = refl
      +0 ⌈⊤⌉ = refl

      1* : ∀ x → ⌈ ε ⌉ * x ≡ x
      1* ⌈⊤⌉ = refl
      1* ⌈ x ⌉ = cong ⌈_⌉ (ε∙ x)

      *1 : ∀ x → x * ⌈ ε ⌉ ≡ x
      *1 ⌈⊤⌉ = refl
      *1 ⌈ x ⌉ = cong ⌈_⌉ (∙ε x)

      0* : ∀ x → 0# * x ≡ 0#
      0* x = refl

    nearSemiring : NearSemiring ℓ
    nearSemiring = record { NS }

    +-comm = ⊓-comm
    open NS

    *0 : ∀ x → _*_ x ⌈⊤⌉ ≡ ⌈⊤⌉
    *0 ⌈ x ⌉ = refl
    *0 ⌈⊤⌉ = refl

    *⟨+⟩ : _*_ Distributesʳ _⊓_
    *⟨+⟩ x y z = *-com x (y ⊓ z) ; ⟨+⟩* y z x ; cong₂ _⊓_ (*-com y x) (*-com z x)

  viterbi : Semiring ℓ
  viterbi = record { Viterbi }

  open TotalOrder totalOrder
    hiding (refl; antisym; _≤_; _≤|≥_; partialOrder; ≤-trans; _≥_; _≰_; _≱_)
    public
