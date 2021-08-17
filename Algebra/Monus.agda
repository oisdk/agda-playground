{-# OPTIONS --safe #-}

-- This is a file for dealing with Monuses: these are monoids that are like the
-- positive half of a group. Much of my info on them comes from these papers:
--
-- * Wehrung, Friedrich. ‘Injective Positively Ordered Monoids I’. Journal of
--   Pure and Applied Algebra 83, no. 1 (11 November 1992): 43–82.
--   https://doi.org/10.1016/0022-4049(92)90104-N.
-- * Wehrung, Friedrich. ‘Embedding Simple Commutative Monoids into Simple
--   Refinement Monoids’. Semigroup Forum 56, no. 1 (January 1998): 104–29.
--   https://doi.org/10.1007/s00233-002-7008-0.
-- * Amer, K. ‘Equationally Complete Classes of Commutative Monoids with Monus’.
--   Algebra Universalis 18, no. 1 (1 February 1984): 129–31.
--   https://doi.org/10.1007/BF01182254.
-- * Wehrung, Friedrich. ‘Metric Properties of Positively Ordered Monoids’.
--   Forum Mathematicum 5, no. 5 (1993).
--   https://doi.org/10.1515/form.1993.5.183.
-- * Wehrung, Friedrich. ‘Restricted Injectivity, Transfer Property and
--   Decompositions of Separative Positively Ordered Monoids.’ Communications in
--   Algebra 22, no. 5 (1 January 1994): 1747–81.
--   https://doi.org/10.1080/00927879408824934.
--
-- These monoids have a preorder defined on them, the algebraic preorder:
-- 
--   x ≤ y = ∃[ z ] (y ≡ x ∙ z)
--
-- The _∸_ operator extracts the z from above, if it exists.

module Algebra.Monus where

open import Prelude
open import Algebra
open import Relation.Binary
open import Path.Reasoning
open import Function.Reasoning

-- Positively ordered monoids.
--
-- These are monoids which have a preorder that respects the monoid operation
-- in a straightforward way.
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
  ≤-congʳ x {y} {z} p = subst₂ _≤_ (comm x y) (comm x z) (≤-cong x p)

  alg-≤-trans : ∀ {x y z k₁ k₂} → y ≡ x ∙ k₁ → z ≡ y ∙ k₂ → z ≡ x ∙ (k₁ ∙ k₂)
  alg-≤-trans {x} {y} {z} {k₁} {k₂} y≡x∙k₁ z≡y∙k₂ =
    z             ≡⟨ z≡y∙k₂ ⟩
    y ∙ k₂        ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
    (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
    x ∙ (k₁ ∙ k₂) ∎

  infix 4 _≺_
  _≺_ : 𝑆 → 𝑆 → Type _
  x ≺ y = ∃[ k ] ((y ≡ x ∙ k) × (k ≢ ε))

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

  <⇒≺ : ∀ x y → y ≰ x → x ≺ y
  <⇒≺ x y x<y with x ≤|≥ y
  ... | inr y≤x = ⊥-elim (x<y y≤x)
  ... | inl (k , y≡x∙k) = λ
    where
    .fst → k
    .snd .fst → y≡x∙k
    .snd .snd k≡ε → x<y (ε , sym (∙ε y ; y≡x∙k ; cong (x ∙_) k≡ε ; ∙ε x))

  infixl 6 _∸_
  _∸_ : 𝑆 → 𝑆 → 𝑆
  x ∸ y = either′ (const ε) fst (x ≤|≥ y)

  x∸y≤x : ∀ x y → x ∸ y ≤ x
  x∸y≤x x y with x ≤|≥ y
  ... | inl (k , p) = positive x
  ... | inr (k , x≡y∙k) = y , x≡y∙k ; comm y k

-- Total Minimal Antisymmetric POM
record TMAPOM ℓ : Type (ℓsuc ℓ) where
  field tmpom : TMPOM ℓ
  open TMPOM tmpom public using (_≤_; _≤|≥_; positive; alg-≤-trans; _≺_; <⇒≺; _∸_; x∸y≤x)
  field antisym : Antisymmetric _≤_

  tapom : TAPOM _ _
  TAPOM.pom tapom = TMPOM.pom tmpom
  TAPOM._≤|≥_ tapom = _≤|≥_
  TAPOM.antisym tapom = antisym

  open TAPOM tapom public hiding (antisym; _≤|≥_; _≤_; positive)

  zeroSumFree : ∀ x y → x ∙ y ≡ ε → x ≡ ε
  zeroSumFree x y x∙y≡ε = antisym (y , sym x∙y≡ε) (positive x)

  ≤‿∸‿cancel : ∀ x y → x ≤ y → (y ∸ x) ∙ x ≡ y
  ≤‿∸‿cancel x y x≤y with y ≤|≥ x
  ... | inl y≤x = ε∙ x ; antisym x≤y y≤x
  ... | inr (k , y≡x∙k) = comm k x ; sym y≡x∙k

  ∸‿comm : ∀ x y → x ∙ (y ∸ x) ≡ y ∙ (x ∸ y)
  ∸‿comm x y with y ≤|≥ x | x ≤|≥ y
  ... | inl y≤x | inl x≤y = cong (_∙ ε) (antisym x≤y y≤x)
  ... | inr (k , y≡x∙k) | inl x≤y = sym y≡x∙k ; sym (∙ε y)
  ... | inl y≤x | inr (k , x≥y) = ∙ε x ; x≥y
  ... | inr (k₁ , y≡x∙k₁) | inr (k₂ , x≡y∙k₂) =
    x ∙ k₁ ≡˘⟨ y≡x∙k₁ ⟩
    y      ≡⟨ antisym  (k₂ , x≡y∙k₂) (k₁ , y≡x∙k₁) ⟩
    x      ≡⟨ x≡y∙k₂ ⟩
    y ∙ k₂ ∎

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

  ∣_-_∣ : 𝑆 → 𝑆 → 𝑆
  ∣ x - y ∣ = (x ∸ y) ∙ (y ∸ x)

  _⊔₂_ : 𝑆 → 𝑆 → 𝑆
  x ⊔₂ y = x ∙ y ∙ ∣ x - y ∣

  _⊓₂_ : 𝑆 → 𝑆 → 𝑆
  x ⊓₂ y = (x ∙ y) ∸ ∣ x - y ∣

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

  ≺⇒< : ∀ x y → x ≺ y → y ≰ x
  ≺⇒< x y (k₁ , y≡x∙k₁ , k₁≢ε) (k₂ , x≡y∙k₂) =
    [ x ∙ ε         ≡⟨ ∙ε x ⟩
      x             ≡⟨ x≡y∙k₂ ⟩
      y ∙ k₂        ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
      (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
      x ∙ (k₁ ∙ k₂) ∎       ]⇒ x ∙ ε ≡ x ∙ (k₁ ∙ k₂)
    ⟨ cancelˡ x ε (k₁ ∙ k₂) ⟩⇒ ε ≡ k₁ ∙ k₂
    ⟨ sym                   ⟩⇒ k₁ ∙ k₂ ≡ ε
    ⟨ zeroSumFree k₁ k₂     ⟩⇒ k₁ ≡ ε
    ⟨ k₁≢ε                  ⟩⇒ ⊥ ⇒∎

  ≤⇒<⇒≢ε : ∀ x y → (x≤y : x ≤ y) → y ≰ x → fst x≤y ≢ ε
  ≤⇒<⇒≢ε x y (k₁ , y≡x∙k₁) y≰x k₁≡ε = y≰x λ
    where
    .fst → ε
    .snd → x      ≡˘⟨ ∙ε x ⟩
           x ∙ ε  ≡˘⟨ cong (x ∙_) k₁≡ε ⟩
           x ∙ k₁ ≡˘⟨ y≡x∙k₁ ⟩
           y      ≡˘⟨ ∙ε y ⟩ 
           y ∙ ε ∎

  ≤-cancelʳ : ∀ x y z → y ∙ x ≤ z ∙ x → y ≤ z
  ≤-cancelʳ x y z (k , z∙x≡y∙x∙k) .fst = k
  ≤-cancelʳ x y z (k , z∙x≡y∙x∙k) .snd = cancelʳ x z (y ∙ k) $
    z ∙ x ≡⟨ z∙x≡y∙x∙k ⟩
    (y ∙ x) ∙ k ≡⟨ assoc y x k ⟩
    y ∙ (x ∙ k) ≡⟨ cong (y ∙_) (comm x k) ⟩
    y ∙ (k ∙ x) ≡˘⟨ assoc y k x ⟩
    (y ∙ k) ∙ x ∎

  ≤-cancelˡ : ∀ x y z → x ∙ y ≤ x ∙ z → y ≤ z
  ≤-cancelˡ x y z (k , x∙z≡x∙y∙k) .fst = k
  ≤-cancelˡ x y z (k , x∙z≡x∙y∙k) .snd =
    cancelˡ x z (y ∙ k) (x∙z≡x∙y∙k ; assoc x y k)

-- Cancellative total minimal antisymmetric pom (has monus)
record CTMAPOM ℓ : Type (ℓsuc ℓ) where
  field tmapom : TMAPOM ℓ
  open TMAPOM tmapom public
  field cancel : Cancellativeˡ _∙_

  module cmm where
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

  open cmm public

  ∸‿cancel : ∀ x y → (x ∙ y) ∸ x ≡ y
  ∸‿cancel x y with (x ∙ y) ≤|≥ x
  ... | inl x∙y≤x = sym (cancel x y ε (antisym x∙y≤x x≤x∙y ; sym (∙ε x)))
  ... | inr (k , x∙y≡x∙k) = sym (cancel x y k x∙y≡x∙k)

  ccmm : CCMM _
  ccmm = record { ∸‿cancel = ∸‿cancel
                ; cmm = record { cmm
                               ; ∸‿comm = ∸‿comm
                               ; commutativeMonoid = commutativeMonoid } }

  open CCMM ccmm public
    using (cancelʳ; cancelˡ; ∸ε; ≺⇒<; ≤⇒<⇒≢ε; _⊔₂_; _⊓₂_)

  2× : 𝑆 → 𝑆
  2× x = x ∙ x

  open import Relation.Binary.Lattice totalOrder

  double-max : ∀ x y → 2× (x ⊔ y) ≡ x ⊔₂ y
  double-max x y with x ≤|≥ y | y ≤|≥ x
  double-max x y | inl x≤y | inl y≤x =
    x ∙ x ≡⟨ cong (x ∙_) (antisym x≤y y≤x) ⟩
    x ∙ y ≡˘⟨ ∙ε (x ∙ y) ⟩
    (x ∙ y) ∙ ε ≡˘⟨ cong ((x ∙ y) ∙_)  (ε∙ ε) ⟩
    (x ∙ y) ∙ (ε ∙ ε) ∎
  double-max x y | inl x≤y | inr (k , y≡x∙k) =
    y ∙ y ≡⟨ cong (y ∙_) y≡x∙k ⟩
    y ∙ (x ∙ k) ≡˘⟨ assoc y x k ⟩
    (y ∙ x) ∙ k ≡⟨ cong (_∙ k) (comm y x) ⟩
    (x ∙ y) ∙ k ≡˘⟨ cong ((x ∙ y) ∙_) (ε∙ k) ⟩
    (x ∙ y) ∙ (ε ∙ k) ∎
  double-max x y | inr (k , x≡y∙k) | inl y≤x =
    x ∙ x ≡⟨ cong (x ∙_) x≡y∙k ⟩
    x ∙ (y ∙ k) ≡˘⟨ assoc x y k ⟩
    (x ∙ y) ∙ k ≡˘⟨ cong ((x ∙ y) ∙_) (∙ε k) ⟩
    (x ∙ y) ∙ (k ∙ ε) ∎
  double-max x y | inr (k₁ , x≡y∙k₁) | inr (k₂ , y≡x∙k₂) =
    x ∙ x ≡⟨ cong (x ∙_) (antisym (k₂ , y≡x∙k₂) (k₁ , x≡y∙k₁)) ⟩
    x ∙ y ≡⟨ cong₂ _∙_ x≡y∙k₁ y≡x∙k₂ ⟩
    (y ∙ k₁) ∙ (x ∙ k₂) ≡˘⟨ assoc (y ∙ k₁) x k₂ ⟩
    ((y ∙ k₁) ∙ x) ∙ k₂ ≡⟨ cong (_∙ k₂) (comm (y ∙ k₁) x) ⟩
    (x ∙ (y ∙ k₁)) ∙ k₂ ≡˘⟨ cong (_∙ k₂) (assoc x y k₁) ⟩
    ((x ∙ y) ∙ k₁) ∙ k₂ ≡⟨ assoc (x ∙ y) k₁ k₂ ⟩
    (x ∙ y) ∙ (k₁ ∙ k₂) ∎

  open import Data.Sigma.Properties

  ≤-prop : ∀ x y → isProp (x ≤ y)
  ≤-prop x y (k₁ , y≡x∙k₁) (k₂ , y≡x∙k₂) = Σ≡Prop (λ _ → total⇒isSet _ _) (cancelˡ x k₁ k₂ (sym y≡x∙k₁ ; y≡x∙k₂))

-- We can construct the viterbi semiring by adjoining a top element to
-- a tapom
module Viterbi {ℓ₁} {ℓ₂} (tapom : TAPOM ℓ₁ ℓ₂) where
  open TAPOM tapom
  open import Relation.Binary.Construct.UpperBound totalOrder
  open import Relation.Binary.Lattice totalOrder

  ⟨⊓⟩∙ : _∙_ Distributesˡ _⊓_
  ⟨⊓⟩∙ x y z with x <? y | (x ∙ z) <? (y ∙ z)
  ... | yes x<y | yes xz<yz = refl
  ... | no  x≮y | no  xz≮yz = refl
  ... | no  x≮y | yes xz<yz = ⊥-elim (<⇒≱ xz<yz (≤-congʳ z (≮⇒≥ x≮y)))
  ... | yes x<y | no  xz≮yz = antisym (≤-congʳ z (<⇒≤ x<y)) (≮⇒≥ xz≮yz)

  ∙⟨⊓⟩ : _∙_ Distributesʳ _⊓_
  ∙⟨⊓⟩ x y z = comm x (y ⊓ z) ; ⟨⊓⟩∙ y z x ; cong₂ _⊓_ (comm y x) (comm z x)

  open UBSugar

  module NS where
    𝑅 = ⌈∙⌉

    0# 1# : 𝑅
    _*_ _+_ : 𝑅 → 𝑅 → 𝑅

    1# = ⌈ ε ⌉

    ⌈⊤⌉   * y     = ⌈⊤⌉
    ⌈ x ⌉ * ⌈⊤⌉   = ⌈⊤⌉
    ⌈ x ⌉ * ⌈ y ⌉ = ⌈ x ∙ y ⌉

    0# = ⌈⊤⌉

    ⌈⊤⌉   + y     = y
    ⌈ x ⌉ + ⌈⊤⌉   = ⌈ x ⌉
    ⌈ x ⌉ + ⌈ y ⌉ = ⌈ x ⊓ y ⌉

    *-assoc : Associative _*_
    *-assoc ⌈⊤⌉   _     _     = refl
    *-assoc ⌈ _ ⌉ ⌈⊤⌉   _     = refl
    *-assoc ⌈ _ ⌉ ⌈ _ ⌉ ⌈⊤⌉   = refl
    *-assoc ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ = cong ⌈_⌉ (assoc x y z)

    *-com : Commutative _*_
    *-com ⌈⊤⌉   ⌈⊤⌉   = refl
    *-com ⌈⊤⌉   ⌈ _ ⌉ = refl
    *-com ⌈ _ ⌉ ⌈⊤⌉   = refl
    *-com ⌈ x ⌉ ⌈ y ⌉ = cong ⌈_⌉ (comm x y)

    ⟨+⟩* : _*_ Distributesˡ _+_
    ⟨+⟩* ⌈⊤⌉   _     _     = refl
    ⟨+⟩* ⌈ _ ⌉ ⌈⊤⌉   ⌈⊤⌉   = refl
    ⟨+⟩* ⌈ _ ⌉ ⌈⊤⌉   ⌈ _ ⌉ = refl
    ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈⊤⌉   = refl
    ⟨+⟩* ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ = cong ⌈_⌉ (⟨⊓⟩∙ x y z)

    +-assoc : Associative _+_
    +-assoc ⌈⊤⌉   _     _     = refl
    +-assoc ⌈ x ⌉ ⌈⊤⌉   _     = refl
    +-assoc ⌈ x ⌉ ⌈ _ ⌉ ⌈⊤⌉   = refl
    +-assoc ⌈ x ⌉ ⌈ y ⌉ ⌈ z ⌉ = cong ⌈_⌉ (⊓-assoc x y z)

    0+ : ∀ x → 0# + x ≡ x
    0+ ⌈⊤⌉   = refl
    0+ ⌈ _ ⌉ = refl

    +0 : ∀ x → x + 0# ≡ x
    +0 ⌈ _ ⌉ = refl
    +0 ⌈⊤⌉   = refl

    1* : ∀ x → 1# * x ≡ x
    1* ⌈⊤⌉   = refl
    1* ⌈ x ⌉ = cong ⌈_⌉ (ε∙ x)

    *1 : ∀ x → x * 1# ≡ x
    *1 ⌈⊤⌉   = refl
    *1 ⌈ x ⌉ = cong ⌈_⌉ (∙ε x)

    0* : ∀ x → 0# * x ≡ 0#
    0* _ = refl

  open NS

  nearSemiring : NearSemiring _
  nearSemiring = record { NS }

  +-comm : Commutative _+_
  +-comm ⌈⊤⌉   ⌈⊤⌉   = refl
  +-comm ⌈⊤⌉   ⌈ _ ⌉ = refl
  +-comm ⌈ _ ⌉ ⌈⊤⌉   = refl
  +-comm ⌈ x ⌉ ⌈ y ⌉ = cong ⌈_⌉ (⊓-comm x y)

  *0 : ∀ x → x * ⌈⊤⌉ ≡ ⌈⊤⌉
  *0 ⌈ _ ⌉ = refl
  *0 ⌈⊤⌉   = refl

  *⟨+⟩ : _*_ Distributesʳ _+_
  *⟨+⟩ x y z = *-com x (y + z) ; ⟨+⟩* y z x ; cong₂ _+_ (*-com y x) (*-com z x)

viterbi : ∀ {ℓ₁ ℓ₂} → TAPOM ℓ₁ ℓ₂ → Semiring ℓ₁
viterbi tapom = record { Viterbi tapom }
