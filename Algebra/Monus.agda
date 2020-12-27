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

  _≤?_ : Total _≤_
  x ≤? y with diff x y
  (x ≤? y) | (⁻ d) , p = inl (d , p)
  (x ≤? y) | ±0 , p = inl (subst (x ≤_) p ≤-refl)
  (x ≤? y) | (⁺ d) , p = inr (d , p)
