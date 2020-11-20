{-# OPTIONS --cubical --safe --prop #-}

open import Algebra
open import Prelude
open import Relation.Binary.Equivalence.PropTruncated

module Algebra.Construct.Cayley.Propositional {a} (mon : Monoid a) where

open Monoid mon

record 𝒞 : Type a where
  constructor cayley
  infixr 7 _⇓_
  field
    _⇓_ : 𝑆 → 𝑆
    small : ∀ x → _⇓_ ε ∙ x ≐ _⇓_ x
open 𝒞 public

⟦_⇓⟧ : 𝒞 → 𝑆
⟦ x ⇓⟧ = x ⇓ ε

⟦_⇑⟧ : 𝑆 → 𝒞
⟦ x ⇑⟧ ⇓ y = x ∙ y
⟦ x ⇑⟧ .small y = ∣ cong (_∙ y) (∙ε x) ∣

ⓔ : 𝒞
ⓔ ⇓ x = x
ⓔ .small x = ∣ ε∙ x ∣

open Reasoning

_⊙_ : 𝒞 → 𝒞 → 𝒞
(x ⊙ y) ⇓ z = x ⇓ y ⇓ z
(x ⊙ y) .small z =
  x ⇓ y ⇓ ε ∙ z       ≐˘⟨ ∙cong (_∙ z) (x .small (y ⇓ ε)) ⟩
  x ⇓ ε ∙ y ⇓ ε ∙ z   ≡⟨ assoc (x ⇓ ε) (y ⇓ ε) z ⟩
  x ⇓ ε ∙ (y ⇓ ε ∙ z) ≐⟨ ∙cong (x ⇓ ε ∙_) (y .small z)  ⟩
  x ⇓ ε ∙ y ⇓ z       ≐⟨ x .small (y ⇓ z) ⟩
  x ⇓ y ⇓ z ∎

⊙-assoc : Associative _⊙_
⊙-assoc x y z = refl

ⓔ⊙ : ∀ x → ⓔ ⊙ x ≡ x
ⓔ⊙ x = refl

⊙ⓔ : ∀ x → x ⊙ ⓔ ≡ x
⊙ⓔ x = refl

cayleyMonoid : Monoid a
Monoid.𝑆 cayleyMonoid = 𝒞
Monoid._∙_ cayleyMonoid = _⊙_
Monoid.ε cayleyMonoid = ⓔ
Monoid.assoc cayleyMonoid = ⊙-assoc
Monoid.ε∙ cayleyMonoid = ⓔ⊙
Monoid.∙ε cayleyMonoid = ⊙ⓔ

open import Data.Sigma.Properties
open import Relation.Nullary.Stable

⇓-≡ : (x y : 𝒞) → _⇓_ x ≡ _⇓_ y → x ≡ y
⇓-≡ f (cayley g q) f≡g = subst (λ (g′ : 𝑆 → 𝑆) → (q′ : ∀ x → g′ ε ∙ x ≐ g′ x) → f ≡ cayley g′ q′) f≡g (λ _ → refl) q

module _ (sIsStable : ∀ {x y : 𝑆} → Stable (x ≡ y)) where
  𝒞-iso : 𝒞 ⇔ 𝑆
  fun 𝒞-iso = ⟦_⇓⟧
  inv 𝒞-iso = ⟦_⇑⟧
  rightInv 𝒞-iso = ∙ε
  leftInv  𝒞-iso x = ⇓-≡ ⟦ ⟦ x ⇓⟧ ⇑⟧  x (λ i y → unsquash sIsStable (x .small y) i)
