{-# OPTIONS --cubical --safe #-}

module Algebra.Monus where

open import Algebra.Construct.Sign
open import Prelude
open import Algebra
open import Relation.Binary

record Monus ℓ : Type (ℓsuc ℓ) where
  field
    commutativeMonoid : CommutativeMonoid ℓ
  open CommutativeMonoid commutativeMonoid public
  field
    diff : (x y : 𝑆) → ∃ (unsign (λ k → (y ≡ x ∙ k)) (x ≡ y) (λ k → (x ≡ y ∙ k)))

  _∸_ : 𝑆 → 𝑆 → Signed 𝑆
  x ∸ y = diff x y .fst

  infix 4 _≤_ _≥_ _<_ _>_
  _≤_ : 𝑆 → 𝑆 → Type ℓ
  x ≤ y = ∃[ z ] (y ≡ x ∙ z)

  _<_ : 𝑆 → 𝑆 → Type ℓ
  x < y = ∃[ z ] ((x ≢ y) × (y ≡ x ∙ z))

  _>_ = flip _<_
  _≥_ = flip _≤_

  ≤-refl : Reflexive _≤_
  ≤-refl = ε , sym (∙ε _)

  open import Path.Reasoning

  ≤-trans : Transitive _≤_
  ≤-trans {x} {y} {z} (k₁ , y≡x∙k₁) (k₂ , z≡y∙k₂) = k₁ ∙ k₂ ,_ $
    z ≡⟨ z≡y∙k₂ ⟩
    y ∙ k₂ ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
    (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
    x ∙ (k₁ ∙ k₂) ∎

  ε≤x : ∀ x → ε ≤ x
  ε≤x x = x , sym (ε∙ x)

  ∙-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z
  ∙-cong x (k , z≡y∙k) = k , cong (x ∙_) z≡y∙k ; sym (assoc x _ k)

  ∙-congʳ : ∀ x {y z} → y ≤ z → y ∙ x ≤ z ∙ x
  ∙-congʳ x {y} {z} p = subst (y ∙ x ≤_) (comm x z) (subst (_≤ x ∙ z) (comm x y) (∙-cong x p))

  _≤?_ : Total _≤_
  x ≤? y with diff x y
  (x ≤? y) | (⁻ d) , p = inl (d , p)
  (x ≤? y) | ±0 , p = inl (subst (x ≤_) p ≤-refl)
  (x ≤? y) | (⁺ d) , p = inr (d , p)

  _≤ᵇ_ : 𝑆 → 𝑆 → Bool
  x ≤ᵇ y = is-l (x ≤? y)

  _⊔_ : 𝑆 → 𝑆 → 𝑆
  x ⊔ y = bool′ x y (x ≤ᵇ y)

  _⊓_ : 𝑆 → 𝑆 → 𝑆
  x ⊓ y = bool′ y x (x ≤ᵇ y)

  Sup : Type _
  Sup = Σ[ Ω ⦂ 𝑆 ] (∀ x → x ≤ Ω )

  module _ (antisym : Antisymmetric _≤_) where
    ⊓-assoc : Associative _⊓_
    ⊓-assoc x y z with x ≤? y | inspect (x ≤ᵇ_) y | y ≤? z | inspect (y ≤ᵇ_) z
    ⊓-assoc x y z | inl x≤y | 〖 xyp 〗 | inl y≤z | 〖 yzp 〗 with x ≤? z
    ⊓-assoc x y z | inl x≤y | 〖 xyp 〗 | inl y≤z | 〖 yzp 〗 | inl x≤z = cong (bool y x) (sym xyp)
    ⊓-assoc x y z | inl x≤y | 〖 xyp 〗 | inl y≤z | 〖 yzp 〗 | inr x≥z = antisym x≥z (≤-trans x≤y y≤z) ; cong (bool y x) (sym xyp)
    ⊓-assoc x y z | inr x≥y | 〖 xyp 〗 | inl y≤z | 〖 yzp 〗 = cong (bool z y) yzp ; cong (bool y x) (sym xyp)
    ⊓-assoc x y z | inl x≤y | 〖 xyp 〗 | inr y≥z | 〖 yzp 〗 = refl
    ⊓-assoc x y z | inr x≥y | 〖 xyp 〗 | inr y≥z | 〖 yzp 〗 with x ≤? z
    ⊓-assoc x y z | inr x≥y | 〖 xyp 〗 | inr y≥z | 〖 yzp 〗 | inl x≤z = let p = ≤-trans y≥z x≥y in cong (bool z y) yzp ; antisym (≤-trans y≥z x≥y) x≤z
    ⊓-assoc x y z | inr x≥y | 〖 xyp 〗 | inr y≥z | 〖 yzp 〗 | inr x≥z = cong (bool z y) yzp

    ⊓-comm : Commutative _⊓_
    ⊓-comm x y with x ≤? y | inspect (x ≤ᵇ_) y | y ≤? x | inspect (y ≤ᵇ_) x
    ⊓-comm x y | inl x₁ | 〖 xyp 〗 | inl x₂ | 〖 yxp 〗 = antisym x₁ x₂
    ⊓-comm x y | inl x₁ | 〖 xyp 〗 | inr x₂ | 〖 yxp 〗 = refl
    ⊓-comm x y | inr x₁ | 〖 xyp 〗 | inl x₂ | 〖 yxp 〗 = refl
    ⊓-comm x y | inr x₁ | 〖 xyp 〗 | inr x₂ | 〖 yxp 〗 = antisym x₁ x₂

    ∙-distrib-⊓ : _∙_ Distributesˡ _⊓_
    ∙-distrib-⊓ x y z with x ≤? y | inspect (x ≤ᵇ_) y | (x ∙ z) ≤? (y ∙ z) | inspect ((x ∙ z) ≤ᵇ_) (y ∙ z)
    ∙-distrib-⊓ x y z | inl x₁ | 〖 xyp 〗 | inl x₂ | 〖 xzyp 〗 = refl
    ∙-distrib-⊓ x y z | inl x₁ | 〖 xyp 〗 | inr x₂ | 〖 xzyp 〗 = antisym (∙-congʳ z x₁) x₂
    ∙-distrib-⊓ x y z | inr x≥y | 〖 xyp 〗 | inl x∙z≤y∙z | 〖 xzyp 〗 = antisym (∙-congʳ z x≥y) x∙z≤y∙z
    ∙-distrib-⊓ x y z | inr x₁ | 〖 xyp 〗 | inr x₂ | 〖 xzyp 〗 = refl

    module _ (sup : Sup) where
      Ω : 𝑆
      Ω = fst sup

      maximal : ∀ x → x ≤ Ω
      maximal = snd sup

      max-sup : ∀ x → Ω ⊓ x ≡ x
      max-sup x with Ω ≤? x
      max-sup x | inl x₁ = antisym x₁ (maximal x)
      max-sup x | inr x₁ = refl

      cmb-sup : ∀ x → Ω ∙ x ≡ Ω
      cmb-sup x = antisym (maximal (Ω ∙ x)) (x , refl)

      viterbi : Semiring ℓ
      NearSemiring.𝑅 (Semiring.nearSemiring viterbi) = 𝑆
      NearSemiring._+_ (Semiring.nearSemiring viterbi) = _⊓_
      NearSemiring._*_ (Semiring.nearSemiring viterbi) = _∙_
      NearSemiring.1# (Semiring.nearSemiring viterbi) = ε
      NearSemiring.0# (Semiring.nearSemiring viterbi) = Ω
      NearSemiring.+-assoc (Semiring.nearSemiring viterbi) = ⊓-assoc
      NearSemiring.*-assoc (Semiring.nearSemiring viterbi) = assoc
      NearSemiring.0+ (Semiring.nearSemiring viterbi) = max-sup
      NearSemiring.+0 (Semiring.nearSemiring viterbi) x = ⊓-comm x Ω ; max-sup x
      NearSemiring.1* (Semiring.nearSemiring viterbi) = ε∙
      NearSemiring.*1 (Semiring.nearSemiring viterbi) = ∙ε
      NearSemiring.0* (Semiring.nearSemiring viterbi) = cmb-sup
      NearSemiring.⟨+⟩* (Semiring.nearSemiring viterbi) = ∙-distrib-⊓
      Semiring.+-comm viterbi = ⊓-comm
      Semiring.*0 viterbi x = comm x Ω ; cmb-sup x
      Semiring.*⟨+⟩ viterbi x y z = comm x (y ⊓ z) ; ∙-distrib-⊓ y z x ; cong₂ _⊓_ (comm y x) (comm z x)
