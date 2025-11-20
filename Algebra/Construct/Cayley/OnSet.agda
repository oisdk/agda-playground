open import Prelude
open import Algebra

module Algebra.Construct.Cayley.OnSet {ℓ} {𝑆 : Type ℓ} (mon : Monoid 𝑆) (sIsSet : isSet 𝑆) where

open Monoid mon

𝒞 : Type ℓ
𝒞 = Σ[ f ⦂ (𝑆 → 𝑆) ] × ∀ x → f ε ∙ x ≡ f x

⟦_⇓⟧ : 𝒞 → 𝑆
⟦ x ⇓⟧ = x .fst ε

⟦_⇑⟧ : 𝑆 → 𝒞
⟦ x ⇑⟧ .fst = _∙_ x
⟦ x ⇑⟧ .snd y = cong (_∙ y) (∙ε x)

ⓔ : 𝒞
ⓔ .fst = id
ⓔ .snd = ε∙

open import Path.Reasoning

_⊙_ : 𝒞 → 𝒞 → 𝒞
(x ⊙ y) .fst z = x .fst (y .fst z)
(x ⊙ y) .snd z =
  x .fst (y .fst ε) ∙ z     ≡˘⟨ cong (_∙ z) (x .snd (y .fst ε)) ⟩
  x .fst ε ∙ y .fst ε ∙ z   ≡⟨ assoc (x .fst ε) (y .fst ε) z ⟩
  x .fst ε ∙ (y .fst ε ∙ z) ≡⟨ cong (x .fst ε ∙_) (y .snd z)  ⟩
  x .fst ε ∙ y .fst z       ≡⟨ x .snd (y .fst z) ⟩
  x .fst (y .fst z) ∎

open import Data.Sigma.Properties
open import Cubical.Foundations.HLevels using (isPropΠ)

𝒞≡ : {x y : 𝒞} → fst x ≡ fst y → x ≡ y
𝒞≡ = Σ≡Prop λ _ → isPropΠ λ _ → sIsSet _ _

⊙-assoc : Associative _⊙_
⊙-assoc _ _ _ = 𝒞≡ refl

ⓔ⊙ : ∀ x → ⓔ ⊙ x ≡ x
ⓔ⊙ _ = 𝒞≡ refl

⊙ⓔ : ∀ x → x ⊙ ⓔ ≡ x
⊙ⓔ _ = 𝒞≡ refl

cayleyMonoid : Monoid 𝒞
Monoid._∙_ cayleyMonoid = _⊙_
Monoid.ε cayleyMonoid = ⓔ
Monoid.assoc cayleyMonoid = ⊙-assoc
Monoid.ε∙ cayleyMonoid = ⓔ⊙
Monoid.∙ε cayleyMonoid = ⊙ⓔ

𝒞-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
𝒞-leftInv x = 𝒞≡ (funExt (snd x))

𝒞-iso : 𝒞 ⇔ 𝑆
fun 𝒞-iso = ⟦_⇓⟧
inv 𝒞-iso = ⟦_⇑⟧
rightInv 𝒞-iso = ∙ε
leftInv 𝒞-iso = 𝒞-leftInv
