{-# OPTIONS --cubical --safe #-}

module Algebra.Monus where

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

  open TotalOrder totalOrder
    hiding (refl; antisym; _≤_; _≤|≥_; partialOrder; ≤-trans)
    renaming (total⇒discrete to _≟_)
    public

  diff≢ε : ∀ {x y} → (x<y : x < y) → fst (<⇒≤ x<y) ≢ ε
  diff≢ε x<y with <⇒≤ x<y
  diff≢ε x<y | k , y≡x∙k = λ k≡ε → irrefl x<y (sym (y≡x∙k ; cong (_ ∙_) k≡ε ; ∙ε _))

  NonZero : Type ℓ
  NonZero = ∃[ x ] (x ≢ ε)

  data Signed : Type ℓ where
    pos : 𝑆 → Signed
    neg : NonZero → Signed

  negate : Signed → Signed
  negate (pos x) with x ≟ ε
  negate (pos x) | no x≢ε = neg (x , x≢ε)
  negate (pos x) | yes _ = pos ε
  negate (neg x) = pos (fst x)

  _⊝_ : 𝑆 → 𝑆 → Signed
  x ⊝ y with y ≤? x
  x ⊝ y | yes x≥y = pos (fst x≥y)
  x ⊝ y | no  x≱y = neg (fst (<⇒≤ x≱y), diff≢ε x≱y)

  _*_ : Signed → Signed → Signed
  pos x * pos y = pos (x ∙ y)
  neg (x , x≢ε) * neg (y , y≢ε) = neg (x ∙ y , x≢ε ∘ zeroSumFree x y)
  pos x * neg y = x ⊝ fst y
  neg x * pos y = y ⊝ fst x

  open import Data.Empty.Properties using (isProp¬)
  open import Data.Sigma.Properties using (ΣProp≡)

  -- *-assoc : Associative _*_
  -- *-assoc x y z = {!!}

  -- *-idˡ : Identityˡ _*_ (pos ε)
  -- *-idˡ (pos x) = cong pos (ε∙ x)
  -- *-idˡ (neg (x , x≢ε)) with x ≤? ε
  -- *-idˡ (neg (x , x≢ε)) | yes x≤ε = ⊥-elim (x≢ε (antisym x≤ε (positive x)))
  -- *-idˡ (neg (x , x≢ε)) | no  x≰ε = let k , p = <⇒≤ x≰ε in cong neg (ΣProp≡ (λ _ → isProp¬ _ ) (sym (ε∙ _) ; sym p ))

  -- *-idʳ : Identityʳ _*_ (pos ε)
  -- *-idʳ = {!!}

  -- *-invʳ : ∀ x → x * negate x ≡ pos ε
  -- *-invʳ = {!!}

  -- *-invˡ : ∀ x → negate x * x ≡ pos ε
  -- *-invˡ = {!!}

  -- *-group : Group ℓ
  -- Monoid.𝑆 (Group.monoid *-group) = Signed
  -- Monoid._∙_ (Group.monoid *-group) = _*_
  -- Monoid.ε (Group.monoid *-group) = pos ε
  -- Monoid.assoc (Group.monoid *-group) = *-assoc
  -- Monoid.ε∙ (Group.monoid *-group) = *-idˡ
  -- Monoid.∙ε (Group.monoid *-group) = *-idʳ
  -- Group.- *-group = negate
  -- Group.∙⁻ *-group = *-invʳ
  -- Group.⁻∙ *-group = *-invˡ

  -- abs : Signed → 𝑆
  -- abs (pos x) = x
  -- abs (neg x) = fst x

  -- sign-abs : ∀ x → abs (pos x) ≡ x
  -- sign-abs x = refl

  -- cancelˡ : Cancellativeˡ _∙_
  -- cancelˡ x y z x∙y≡x∙z = cong abs (Group.cancelˡ *-group (pos x) (pos y) (pos z) (cong pos x∙y≡x∙z))

  -- cancelʳ : Cancellativeʳ _∙_
  -- cancelʳ x y z x∙y≡x∙z = cong abs (Group.cancelʳ *-group (pos x) (pos y) (pos z) (cong pos x∙y≡x∙z))

  -- -- _≺_ : 𝑆 → 𝑆 → Type _

  -- -- x ≺ y = Σ[ x≤y ⦂ x ≤ y ] (fst x≤y ≢ ε)

  -- -- <⇒≺ : ∀ {x y} → x < y → x ≺ y
  -- -- <⇒≺ x<y = <⇒≤ x<y , diff≢ε x<y

  -- -- ≺⇒< : ∀ {x y} → x ≺ y → x < y
  -- -- ≺⇒< {x} {y} ((k₁ , y≡x∙k₁) , k₁≢ε) (k₂ , x≡y∙k₂) = {!!}
  -- --   where
  -- --   p : x ≡ x ∙ (k₁ ∙ k₂)
  -- --   p = x≡y∙k₂ ; cong (_∙ k₂) y≡x∙k₁ ; assoc x k₁ k₂

  -- --   q : k₁ ∙ k₂ ≢ ε
  -- --   q = k₁≢ε ∘ zeroSumFree k₁ k₂

  -- -- Sup : Type _
  -- -- Sup = Σ[ Ω ⦂ 𝑆 ] (∀ x → x ≤ Ω )
  -- -- -- ∙-distrib-⊓ : _∙_ Distributesˡ _⊓_
  -- -- -- ∙-distrib-⊓ x y z with x <? y | (x ∙ z) <? (y ∙ z)
  -- -- -- ∙-distrib-⊓ x y z | yes x₁  | yes x₂ = refl
  -- -- -- ∙-distrib-⊓ x y z | yes x₁  | no x₂  = antisym (∙-congʳ z (<⇒≤ x₁)) (≮⇒≥ x₂)
  -- -- -- ∙-distrib-⊓ x y z | no  x≥y | yes x∙z≤y∙z = antisym (∙-congʳ z (≮⇒≥ x≥y)) (<⇒≤ x∙z≤y∙z)
  -- -- -- ∙-distrib-⊓ x y z | no  x₁  | no x₂ = refl

  -- -- -- module _ (sup : Sup) where
  -- -- --   Ω : 𝑆
  -- -- --   Ω = fst sup

  -- -- --   maximal : ∀ x → x ≤ Ω
  -- -- --   maximal = snd sup

  -- -- --   max-sup : ∀ x → Ω ⊓ x ≡ x
  -- -- --   max-sup x with Ω <? x
  -- -- --   max-sup x | yes x₁ = ⊥-elim (x₁ (maximal x))
  -- -- --   max-sup x | no  x₁ = refl

  -- -- --   cmb-sup : ∀ x → Ω ∙ x ≡ Ω
  -- -- --   cmb-sup x = antisym (maximal (Ω ∙ x)) (x , refl)

  -- -- --   viterbi : Semiring ℓ
  -- -- --   NearSemiring.𝑅 (Semiring.nearSemiring viterbi) = 𝑆
  -- -- --   NearSemiring._+_ (Semiring.nearSemiring viterbi) = _⊓_
  -- -- --   NearSemiring._*_ (Semiring.nearSemiring viterbi) = _∙_
  -- -- --   NearSemiring.1# (Semiring.nearSemiring viterbi) = ε
  -- -- --   NearSemiring.0# (Semiring.nearSemiring viterbi) = Ω
  -- -- --   NearSemiring.+-assoc (Semiring.nearSemiring viterbi) = ⊓-assoc
  -- -- --   NearSemiring.*-assoc (Semiring.nearSemiring viterbi) = assoc
  -- -- --   NearSemiring.0+ (Semiring.nearSemiring viterbi) = max-sup
  -- -- --   NearSemiring.+0 (Semiring.nearSemiring viterbi) x = ⊓-comm x Ω ; max-sup x
  -- -- --   NearSemiring.1* (Semiring.nearSemiring viterbi) = ε∙
  -- -- --   NearSemiring.*1 (Semiring.nearSemiring viterbi) = ∙ε
  -- -- --   NearSemiring.0* (Semiring.nearSemiring viterbi) = cmb-sup
  -- -- --   NearSemiring.⟨+⟩* (Semiring.nearSemiring viterbi) = ∙-distrib-⊓
  -- -- --   Semiring.+-comm viterbi = ⊓-comm
  -- -- --   Semiring.*0 viterbi x = comm x Ω ; cmb-sup x
  -- -- --   Semiring.*⟨+⟩ viterbi x y z = comm x (y ⊓ z) ; ∙-distrib-⊓ y z x ; cong₂ _⊓_ (comm y x) (comm z x)
