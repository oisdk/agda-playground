{-# OPTIONS --cubical --safe #-}

module Algebra.Monus where

open import Algebra.Construct.Sign
open import Prelude
open import Algebra
open import Relation.Binary
open import Path.Reasoning

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
  PartialOrder._≤_ partialOrder = _≤_
  PartialOrder.refl partialOrder = ≤-refl
  PartialOrder.antisym partialOrder = antisym
  PartialOrder.trans partialOrder = ≤-trans

  totalOrder : TotalOrder 𝑆 ℓ ℓ
  totalOrder = fromPartialOrder partialOrder _≤|≥_

  open TotalOrder totalOrder hiding (refl; antisym; _≤_; _≤|≥_; partialOrder; ≤-trans) public

  -- Sup : Type _
  -- Sup = Σ[ Ω ⦂ 𝑆 ] (∀ x → x ≤ Ω )
  -- -- ∙-distrib-⊓ : _∙_ Distributesˡ _⊓_
  -- -- ∙-distrib-⊓ x y z with x <? y | (x ∙ z) <? (y ∙ z)
  -- -- ∙-distrib-⊓ x y z | yes x₁  | yes x₂ = refl
  -- -- ∙-distrib-⊓ x y z | yes x₁  | no x₂  = antisym (∙-congʳ z (<⇒≤ x₁)) (≮⇒≥ x₂)
  -- -- ∙-distrib-⊓ x y z | no  x≥y | yes x∙z≤y∙z = antisym (∙-congʳ z (≮⇒≥ x≥y)) (<⇒≤ x∙z≤y∙z)
  -- -- ∙-distrib-⊓ x y z | no  x₁  | no x₂ = refl

  -- -- module _ (sup : Sup) where
  -- --   Ω : 𝑆
  -- --   Ω = fst sup

  -- --   maximal : ∀ x → x ≤ Ω
  -- --   maximal = snd sup

  -- --   max-sup : ∀ x → Ω ⊓ x ≡ x
  -- --   max-sup x with Ω <? x
  -- --   max-sup x | yes x₁ = ⊥-elim (x₁ (maximal x))
  -- --   max-sup x | no  x₁ = refl

  -- --   cmb-sup : ∀ x → Ω ∙ x ≡ Ω
  -- --   cmb-sup x = antisym (maximal (Ω ∙ x)) (x , refl)

  -- --   viterbi : Semiring ℓ
  -- --   NearSemiring.𝑅 (Semiring.nearSemiring viterbi) = 𝑆
  -- --   NearSemiring._+_ (Semiring.nearSemiring viterbi) = _⊓_
  -- --   NearSemiring._*_ (Semiring.nearSemiring viterbi) = _∙_
  -- --   NearSemiring.1# (Semiring.nearSemiring viterbi) = ε
  -- --   NearSemiring.0# (Semiring.nearSemiring viterbi) = Ω
  -- --   NearSemiring.+-assoc (Semiring.nearSemiring viterbi) = ⊓-assoc
  -- --   NearSemiring.*-assoc (Semiring.nearSemiring viterbi) = assoc
  -- --   NearSemiring.0+ (Semiring.nearSemiring viterbi) = max-sup
  -- --   NearSemiring.+0 (Semiring.nearSemiring viterbi) x = ⊓-comm x Ω ; max-sup x
  -- --   NearSemiring.1* (Semiring.nearSemiring viterbi) = ε∙
  -- --   NearSemiring.*1 (Semiring.nearSemiring viterbi) = ∙ε
  -- --   NearSemiring.0* (Semiring.nearSemiring viterbi) = cmb-sup
  -- --   NearSemiring.⟨+⟩* (Semiring.nearSemiring viterbi) = ∙-distrib-⊓
  -- --   Semiring.+-comm viterbi = ⊓-comm
  -- --   Semiring.*0 viterbi x = comm x Ω ; cmb-sup x
  -- --   Semiring.*⟨+⟩ viterbi x y z = comm x (y ⊓ z) ; ∙-distrib-⊓ y z x ; cong₂ _⊓_ (comm y x) (comm z x)
