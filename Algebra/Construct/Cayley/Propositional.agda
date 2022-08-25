{-# OPTIONS --cubical --safe --prop #-}

open import Algebra
open import Prelude
open import Relation.Binary.Equivalence.PropTruncated

module Algebra.Construct.Cayley.Propositional {a} {𝑆 : Type a} (mon : Monoid 𝑆) where

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

module _ where
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

cayleyMonoid : Monoid 𝒞
Monoid._∙_ cayleyMonoid = _⊙_
Monoid.ε cayleyMonoid = ⓔ
Monoid.assoc cayleyMonoid = ⊙-assoc
Monoid.ε∙ cayleyMonoid = ⓔ⊙
Monoid.∙ε cayleyMonoid = ⊙ⓔ

open import Data.Sigma.Properties
open import Relation.Nullary.Stable

𝒞≡ : {x y : 𝒞} → (∀ z → x ⇓ z ≡ y ⇓ z) → x ≡ y
𝒞≡ { f } { cayley g q } f≡g =
  subst
    (λ (g′ : 𝑆 → 𝑆) → (q′ : ∀ x → g′ ε ∙ x ≐ g′ x) → f ≡ cayley g′ q′)
    (funExt f≡g)
    (λ _ → refl)
    q

∙-homo : ∀ x y → ⟦ x ∙ y ⇑⟧ ≡ ⟦ x ⇑⟧ ⊙ ⟦ y ⇑⟧
∙-homo x y = 𝒞≡ (assoc x y)

ε-homo : ⟦ ε ⇑⟧ ≡ ⓔ
ε-homo = 𝒞≡ ε∙

homo-to : MonoidHomomorphism mon ⟶ cayleyMonoid
MonoidHomomorphism_⟶_.f homo-to = ⟦_⇑⟧
MonoidHomomorphism_⟶_.∙-homo homo-to = ∙-homo
MonoidHomomorphism_⟶_.ε-homo homo-to = ε-homo

ⓔ-homo : ⟦ ⓔ ⇓⟧ ≡ ε
ⓔ-homo = refl

module _ (sIsStable : ∀ {x y : 𝑆} → Stable (x ≡ y)) where
  ⊙-homo : ∀ x y → ⟦ x ⊙ y ⇓⟧ ≡ ⟦ x ⇓⟧ ∙ ⟦ y ⇓⟧
  ⊙-homo x y = sym (unsquash sIsStable (x .small ⟦ y ⇓⟧))

  𝒞-iso : 𝒞 ⇔ 𝑆
  fun 𝒞-iso = ⟦_⇓⟧
  inv 𝒞-iso = ⟦_⇑⟧
  rightInv 𝒞-iso = ∙ε
  leftInv  𝒞-iso x = 𝒞≡ λ y → unsquash sIsStable (x .small y)

  homo-from : MonoidHomomorphism cayleyMonoid ⟶ mon
  MonoidHomomorphism_⟶_.f homo-from = ⟦_⇓⟧
  MonoidHomomorphism_⟶_.∙-homo homo-from = ⊙-homo
  MonoidHomomorphism_⟶_.ε-homo homo-from = ⓔ-homo
