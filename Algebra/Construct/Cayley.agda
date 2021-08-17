{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

module Algebra.Construct.Cayley {a} (mon : Monoid a) where

open Monoid mon

𝒞 : Type a
𝒞 = Σ[ f ⦂ (𝑆 → 𝑆) ] × ∀ x → ∥ f ε ∙ x ≡ f x ∥


⟦_⇓⟧ : 𝒞 → 𝑆
⟦ x ⇓⟧ = x .fst ε

⟦_⇑⟧ : 𝑆 → 𝒞
⟦ x ⇑⟧ .fst y = x ∙ y
⟦ x ⇑⟧ .snd y = ∣ cong (_∙ y) (∙ε x) ∣

ⓔ : 𝒞
ⓔ .fst x = x
ⓔ .snd x = ∣ ε∙ x ∣

open import Relation.Binary
open import HITs.PropositionalTruncation.Equivalence
open import Relation.Binary.Equivalence.Reasoning (trunc-equivalence (≡-equivalence {A = 𝑆}))

_⊙_ : 𝒞 → 𝒞 → 𝒞
(x ⊙ y) .fst z = x .fst (y .fst z)
(x ⊙ y) .snd z =
  x .fst (y .fst ε) ∙ z     ≋˘⟨ cong (_∙ z) ∥$∥ (x .snd (y .fst ε)) ⟩
  x .fst ε ∙ y .fst ε ∙ z   ≡⟨ assoc (x .fst ε) (y .fst ε) z ⟩
  x .fst ε ∙ (y .fst ε ∙ z) ≋⟨ cong (x .fst ε ∙_) ∥$∥ (y .snd z)  ⟩
  x .fst ε ∙ y .fst z       ≋⟨ x .snd (y .fst z) ⟩
  x .fst (y .fst z) ∎

⊙-assoc : Associative _⊙_
⊙-assoc x y z i .fst k = x .fst (y .fst (z .fst k))
⊙-assoc x y z i .snd k = squash (((x ⊙ y) ⊙ z) .snd k) ((x ⊙ (y ⊙ z)) .snd k) i

ⓔ⊙ : ∀ x → ⓔ ⊙ x ≡ x
ⓔ⊙ x i .fst y = x .fst y
ⓔ⊙ x i .snd y = squash ((ⓔ ⊙ x) .snd y) (x .snd y) i

⊙ⓔ : ∀ x → x ⊙ ⓔ ≡ x
⊙ⓔ x i .fst y = x .fst y
⊙ⓔ x i .snd y = squash ((x ⊙ ⓔ) .snd y) (x .snd y) i

cayleyMonoid : Monoid a
Monoid.𝑆 cayleyMonoid = 𝒞
Monoid._∙_ cayleyMonoid = _⊙_
Monoid.ε cayleyMonoid = ⓔ
Monoid.assoc cayleyMonoid = ⊙-assoc
Monoid.ε∙ cayleyMonoid = ⓔ⊙
Monoid.∙ε cayleyMonoid = ⊙ⓔ

open import Data.Sigma.Properties

module _ (sIsSet : isSet 𝑆) where
  𝒞-leftInv-fst : ∀ x y → ⟦ ⟦ x ⇓⟧ ⇑⟧ .fst y ≡ x .fst y
  𝒞-leftInv-fst x y = rec (sIsSet (x .fst ε ∙ y) (x .fst y)) id (x .snd y)

  𝒞-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
  𝒞-leftInv x = Σ≡Prop (λ f xs ys → funExt λ x → squash (xs x) (ys x)) (funExt (𝒞-leftInv-fst x))

  𝒞-iso : 𝒞 ⇔ 𝑆
  fun 𝒞-iso = ⟦_⇓⟧
  inv 𝒞-iso = ⟦_⇑⟧
  rightInv 𝒞-iso = ∙ε
  leftInv 𝒞-iso = 𝒞-leftInv
