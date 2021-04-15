{-# OPTIONS --cubical --safe #-}

module Algebra.Monus where

open import Prelude
open import Algebra
open import Relation.Binary
open import Path.Reasoning
open import Function.Reasoning

-- Positively ordered monoids
record POM ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field commutativeMonoid : CommutativeMonoid ℓ₁
  open CommutativeMonoid commutativeMonoid public
  field preorder : Preorder 𝑆 ℓ₂
  open Preorder preorder public renaming (refl to ≤-refl)
  field
    positive : ∀ x → ε ≤ x
    ≤-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z

  x≤x∙y : ∀ {x y} → x ≤ x ∙ y
  x≤x∙y {x} {y} = subst (_≤ x ∙ y) (∙ε x) (≤-cong x (positive y))

  ≤-congʳ : ∀ x {y z} → y ≤ z → y ∙ x ≤ z ∙ x
  ≤-congʳ x {y} {z} p = subst (y ∙ x ≤_) (comm x z) (subst (_≤ x ∙ z) (comm x y) (≤-cong x p))

  alg-≤-trans : ∀ {x y z k₁ k₂} → y ≡ x ∙ k₁ → z ≡ y ∙ k₂ → z ≡ x ∙ (k₁ ∙ k₂)
  alg-≤-trans {x} {y} {z} {k₁} {k₂} y≡x∙k₁ z≡y∙k₂ =
    z             ≡⟨ z≡y∙k₂ ⟩
    y ∙ k₂        ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
    (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
    x ∙ (k₁ ∙ k₂) ∎

-- Total Antisymmetric POM
record TAPOM ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field pom : POM ℓ₁ ℓ₂
  open POM pom public using (preorder; _≤_; ≤-cong; ≤-congʳ; x≤x∙y; commutativeMonoid; positive)
  open CommutativeMonoid commutativeMonoid public
  field
    _≤|≥_   : Total _≤_
    antisym : Antisymmetric _≤_

  totalOrder : TotalOrder 𝑆 ℓ₂ ℓ₂
  totalOrder = fromPartialOrder (record { preorder = preorder ; antisym = antisym }) _≤|≥_
  open TotalOrder totalOrder public hiding (_≤|≥_; antisym) renaming (refl to ≤-refl)


-- Every commutative monoid generates a positively ordered monoid
-- called the "algebraic" or "minimal" pom
module AlgebraicPOM {ℓ} (mon : CommutativeMonoid ℓ) where
  commutativeMonoid = mon
  open CommutativeMonoid mon

  infix 4 _≤_
  _≤_ : 𝑆 → 𝑆 → Type _
  x ≤ y = ∃[ z ] (y ≡ x ∙ z)

  -- The snd here is the same proof as alg-≤-trans, so could be refactored out.
  ≤-trans : Transitive _≤_
  ≤-trans (k₁ , _) (k₂ , _) .fst = k₁ ∙ k₂
  ≤-trans {x} {y} {z} (k₁ , y≡x∙k₁) (k₂ , z≡y∙k₂) .snd =
    z             ≡⟨ z≡y∙k₂ ⟩
    y ∙ k₂        ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
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

algebraic-pom : ∀ {ℓ} → CommutativeMonoid ℓ → POM ℓ ℓ
algebraic-pom mon = record { AlgebraicPOM mon }

-- Total Minimal POM
record TMPOM ℓ : Type (ℓsuc ℓ) where
  field commutativeMonoid : CommutativeMonoid ℓ

  pom : POM _ _
  pom = algebraic-pom commutativeMonoid

  open POM pom public

  infix 4 _≤|≥_
  field _≤|≥_ : Total _≤_

-- Total Minimal Antisymmetric POM
record TMAPOM ℓ : Type (ℓsuc ℓ) where
  field tmpom : TMPOM ℓ
  open TMPOM tmpom public using (_≤_; _≤|≥_; positive; alg-≤-trans)
  field antisym : Antisymmetric _≤_

  tapom : TAPOM _ _
  TAPOM.pom tapom = TMPOM.pom tmpom
  TAPOM._≤|≥_ tapom = _≤|≥_
  TAPOM.antisym tapom = antisym

  open TAPOM tapom public hiding (antisym; _≤|≥_; _≤_; positive)

  zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
  zeroSumFree x y x∙y≡ε = antisym (y , sym x∙y≡ε) (positive x)

-- Commutative Monoids with Monus
record CMM ℓ : Type (ℓsuc ℓ) where
  field commutativeMonoid : CommutativeMonoid ℓ

  pom : POM _ _
  pom = algebraic-pom commutativeMonoid

  open POM pom public

  field _∸_ : 𝑆 → 𝑆 → 𝑆
  infixl 6 _∸_
  field
    ∸‿comm  : ∀ x y → x ∙ (y ∸ x) ≡ y ∙ (x ∸ y)
    ∸‿assoc : ∀ x y z → (x ∸ y) ∸ z ≡ x ∸ (y ∙ z)
    ∸‿inv   : ∀ x → x ∸ x ≡ ε
    ε∸      : ∀ x → ε ∸ x ≡ ε

  ∸ε : ∀ x → x ∸ ε ≡ x
  ∸ε x =
    x ∸ ε       ≡˘⟨ ε∙ (x ∸ ε) ⟩
    ε ∙ (x ∸ ε) ≡⟨ ∸‿comm ε x ⟩
    x ∙ (ε ∸ x) ≡⟨ cong (x ∙_) (ε∸ x) ⟩
    x ∙ ε       ≡⟨ ∙ε x ⟩
    x ∎


  ∸≤ : ∀ x y → x ≤ y → x ∸ y ≡ ε
  ∸≤ x y (k , y≡x∙k) =
    x ∸ y       ≡⟨ cong (x ∸_) y≡x∙k ⟩
    x ∸ (x ∙ k) ≡˘⟨ ∸‿assoc x x k ⟩
    (x ∸ x) ∸ k ≡⟨ cong (_∸ k) (∸‿inv x) ⟩
    ε ∸ k       ≡⟨ ε∸ k ⟩
    ε ∎

-- Cancellative Commutative Monoids with Monus
record CCMM ℓ : Type (ℓsuc ℓ) where
  field cmm : CMM ℓ
  open CMM cmm public

  field ∸‿cancel : ∀ x y → (x ∙ y) ∸ x ≡ y

  cancelˡ : Cancellativeˡ _∙_
  cancelˡ x y z x∙y≡x∙z =
    y           ≡˘⟨ ∸‿cancel x y ⟩
    (x ∙ y) ∸ x ≡⟨ cong (_∸ x) x∙y≡x∙z ⟩
    (x ∙ z) ∸ x ≡⟨ ∸‿cancel x z ⟩
    z ∎

  cancelʳ : Cancellativeʳ _∙_
  cancelʳ x y z y∙x≡z∙x =
    y           ≡˘⟨ ∸‿cancel x y ⟩
    (x ∙ y) ∸ x ≡⟨ cong (_∸ x) (comm x y) ⟩
    (y ∙ x) ∸ x ≡⟨ cong (_∸ x) y∙x≡z∙x ⟩
    (z ∙ x) ∸ x ≡⟨ cong (_∸ x) (comm z x) ⟩
    (x ∙ z) ∸ x ≡⟨ ∸‿cancel x z ⟩
    z ∎

  zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
  zeroSumFree x y x∙y≡ε =
    x           ≡˘⟨ ∸‿cancel y x ⟩
    (y ∙ x) ∸ y ≡⟨ cong (_∸ y) (comm y x) ⟩
    (x ∙ y) ∸ y ≡⟨ cong (_∸ y) x∙y≡ε ⟩
    ε ∸ y       ≡⟨ ε∸ y ⟩
    ε ∎

  antisym : Antisymmetric _≤_
  antisym {x} {y} (k₁ , y≡x∙k₁) (k₂ , x≡y∙k₂) =
      x      ≡⟨ x≡y∙k₂ ⟩
      y ∙ k₂ ≡⟨ [ lemma                 ]⇒ y ∙ ε   ≡ y ∙ (k₂ ∙ k₁)
                ⟨ cancelˡ y ε (k₂ ∙ k₁) ⟩⇒ ε       ≡ k₂ ∙ k₁
                ⟨ sym                   ⟩⇒ k₂ ∙ k₁ ≡ ε
                ⟨ zeroSumFree k₂ k₁     ⟩⇒ k₂      ≡ ε
                ⟨ cong (y ∙_)           ⟩⇒ y ∙ k₂  ≡ y ∙ ε ⇒∎ ⟩
      y ∙ ε  ≡⟨ ∙ε y ⟩
      y ∎
    where
    lemma = ∙ε y ; alg-≤-trans x≡y∙k₂ y≡x∙k₁

  partialOrder : PartialOrder _ _
  PartialOrder.preorder partialOrder = preorder
  PartialOrder.antisym partialOrder = antisym

module POMToMonus {ℓ} (tmapom : TMAPOM ℓ) (cancel : Cancellativeˡ (TMAPOM._∙_ tmapom)) where
  open TMAPOM tmapom

  module NonCancel where
    _∸_ : 𝑆 → 𝑆 → 𝑆
    x ∸ y = either (const ε) fst (x ≤|≥ y)

    ∸≤ : ∀ x y → x ≤ y → x ∸ y ≡ ε
    ∸≤ x y x≤y with x ≤|≥ y
    ∸≤ x y x≤y | inl _ = refl
    ∸≤ x y (k₁ , y≡x∙k₁) | inr (k₂ , x≡y∙k₂) =
      [ lemma                ]⇒ y ∙ ε   ≡ y ∙ (k₂ ∙ k₁)
      ⟨ cancel y ε (k₂ ∙ k₁) ⟩⇒ ε       ≡ k₂ ∙ k₁
      ⟨ sym                  ⟩⇒ k₂ ∙ k₁ ≡ ε
      ⟨ zeroSumFree k₂ k₁    ⟩⇒ k₂      ≡ ε ⇒∎
      where
      lemma = ∙ε y ; alg-≤-trans x≡y∙k₂ y≡x∙k₁

    ∸‿inv : ∀ x → x ∸ x ≡ ε
    ∸‿inv x = ∸≤ x x ≤-refl

    ε∸ : ∀ x → ε ∸ x ≡ ε
    ε∸ x = ∸≤ ε x (positive x)

    ∸‿comm : ∀ x y → x ∙ (y ∸ x) ≡ y ∙ (x ∸ y)
    ∸‿comm x y with y ≤|≥ x | x ≤|≥ y
    ∸‿comm x y | inl y≤x | inl x≤y = cong (_∙ ε) (antisym x≤y y≤x)
    ∸‿comm x y | inr (k , y≡x∙k) | inl x≤y = sym y≡x∙k ; sym (∙ε y)
    ∸‿comm x y | inl y≤x | inr (k , x≥y) = ∙ε x ; x≥y
    ∸‿comm x y | inr (k₁ , y≡x∙k₁) | inr (k₂ , x≡y∙k₂) =
      x ∙ k₁ ≡˘⟨ y≡x∙k₁ ⟩
      y      ≡⟨ antisym  (k₂ , x≡y∙k₂) (k₁ , y≡x∙k₁) ⟩
      x      ≡⟨ x≡y∙k₂ ⟩
      y ∙ k₂ ∎

    ∸‿assoc : ∀ x y z → (x ∸ y) ∸ z ≡ x ∸ (y ∙ z)
    ∸‿assoc x y z with x ≤|≥ y
    ∸‿assoc x y z | inl x≤y  = ε∸ z ; sym (∸≤ x (y ∙ z) (≤-trans x≤y x≤x∙y))
    ∸‿assoc x y z | inr x≥y with x ≤|≥ y ∙ z
    ∸‿assoc x y z | inr (k₁ , x≡y∙k₁) | inl (k₂ , y∙z≡x∙k₂) = ∸≤ k₁ z (k₂ , lemma)
      where
      lemma : z ≡ k₁ ∙ k₂
      lemma = cancel y z (k₁ ∙ k₂) (alg-≤-trans x≡y∙k₁ y∙z≡x∙k₂)

    ∸‿assoc x y z | inr (k , x≡y∙k) | inr x≥y∙z with k ≤|≥ z
    ∸‿assoc x y z | inr (k₁ , x≡y∙k₁) | inr (k₂ , x≡y∙z∙k₂) | inl (k₃ , z≡k₁∙k₃) =
        [ lemma₁            ]⇒ ε       ≡ k₂ ∙ k₃
        ⟨ sym               ⟩⇒ k₂ ∙ k₃ ≡ ε
        ⟨ zeroSumFree k₂ k₃ ⟩⇒ k₂      ≡ ε
        ⟨ sym               ⟩⇒ ε       ≡ k₂ ⇒∎
      where
      lemma₃ =
        y ∙ k₁       ≡˘⟨ x≡y∙k₁ ⟩
        x            ≡⟨ x≡y∙z∙k₂ ⟩
        (y ∙ z) ∙ k₂ ≡⟨ assoc y z k₂ ⟩
        y ∙ (z ∙ k₂) ∎

      lemma₂ =
        k₁ ∙ ε         ≡⟨ ∙ε k₁ ⟩
        k₁             ≡⟨ alg-≤-trans z≡k₁∙k₃ (cancel y k₁ (z ∙ k₂) lemma₃) ⟩
        k₁ ∙ (k₃ ∙ k₂) ∎

      lemma₁ =
        ε       ≡⟨ cancel k₁ ε (k₃ ∙ k₂) lemma₂ ⟩
        k₃ ∙ k₂ ≡⟨ comm k₃ k₂ ⟩
        k₂ ∙ k₃ ∎

    ∸‿assoc x y z | inr (k₁ , x≡y∙k₁) | inr (k₂ , x≡y∙z∙k₂) | inr (k₃ , k₁≡z∙k₃) =
        cancel z k₃ k₂ lemma₂
      where
      lemma₁ =
        y ∙ k₁       ≡˘⟨ x≡y∙k₁ ⟩
        x            ≡⟨ x≡y∙z∙k₂ ⟩
        (y ∙ z) ∙ k₂ ≡⟨ assoc y z k₂ ⟩
        y ∙ (z ∙ k₂) ∎

      lemma₂ =
        z ∙ k₃ ≡˘⟨ k₁≡z∙k₃ ⟩
        k₁     ≡⟨ cancel y k₁ (z ∙ k₂) lemma₁ ⟩
        z ∙ k₂ ∎

  cmm : CMM _
  cmm = record { NonCancel ; commutativeMonoid = commutativeMonoid }

  open NonCancel

  ∸‿cancel : ∀ x y → (x ∙ y) ∸ x ≡ y
  ∸‿cancel x y with (x ∙ y) ≤|≥ x
  ∸‿cancel x y | inl x∙y≤x = sym (cancel x y ε (antisym x∙y≤x x≤x∙y ; sym (∙ε x)))
  ∸‿cancel x y | inr (k , x∙y≡x∙k) = sym (cancel x y k x∙y≡x∙k)

pomToMonus : (tmapom : TMAPOM a) → (cancel : Cancellativeˡ (TMAPOM._∙_ tmapom)) → CCMM a
pomToMonus t c = record { POMToMonus t c }

module Viterbi {ℓ₁} {ℓ₂} (tapom : TAPOM ℓ₁ ℓ₂) where
  open TAPOM tapom
  open import Relation.Binary.Construct.UpperBound totalOrder
  open import Relation.Binary.Lattice ub-ord
  open UBSugar

  module NS where
    _*_ : ⌈∙⌉ → ⌈∙⌉ → ⌈∙⌉
    x * y = ⦇ x ∙ y ⦈

    *-assoc : Associative _*_
    *-assoc ⌈⊤⌉ ⌈⊤⌉ ⌈⊤⌉ = refl
    *-assoc ⌈⊤⌉ ⌈⊤⌉ ⌈ x ⌉ = refl
    *-assoc ⌈⊤⌉ ⌈ x ⌉ ⌈⊤⌉ = refl
    *-assoc ⌈⊤⌉ ⌈ _ ⌉ ⌈ _ ⌉ = refl
    *-assoc ⌈ _ ⌉ ⌈⊤⌉ ⌈⊤⌉ = refl
    *-assoc ⌈ _ ⌉ ⌈⊤⌉ ⌈ _ ⌉ = refl
    *-assoc ⌈ _ ⌉ ⌈ _ ⌉ ⌈⊤⌉ = refl
    *-assoc ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ = cong ⌈_⌉ (assoc x y z)

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
    ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ with x <? y | (x ∙ z) <? (y ∙ z)
    ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | yes x<y | yes xz<yz = refl
    ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | no  x≮y | no  xz≮yz = refl
    ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | no  x≮y | yes xz<yz = ⊥-elim (<⇒≱ xz<yz (≤-congʳ z (≮⇒≥ x≮y)))
    ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ | yes x<y | no  xz≮yz = TotalOrder.antisym ub-ord (≤-congʳ z (<⇒≤ x<y)) (≮⇒≥ xz≮yz)

    𝑅 = ⌈∙⌉

    1# = ⌈ ε ⌉

    0# : 𝑅
    0# = ⌈⊤⌉

    +-assoc = ⊓-assoc

    0+ : ∀ x → ⌈⊤⌉ ⊓ x ≡ x
    0+ ⌈⊤⌉ = refl
    0+ ⌈ x ⌉ = refl

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

  nearSemiring : NearSemiring _
  nearSemiring = record { NS ; _+_ = _⊓_ }

  +-comm = ⊓-comm
  open NS

  *0 : ∀ x → x * ⌈⊤⌉ ≡ ⌈⊤⌉
  *0 ⌈ x ⌉ = refl
  *0 ⌈⊤⌉ = refl

  *⟨+⟩ : _*_ Distributesʳ _⊓_
  *⟨+⟩ x y z = *-com x (y ⊓ z) ; ⟨+⟩* y z x ; cong₂ _⊓_ (*-com y x) (*-com z x)

viterbi : ∀ {ℓ₁ ℓ₂} → TAPOM ℓ₁ ℓ₂ → Semiring ℓ₁
viterbi tapom = record { Viterbi tapom }
