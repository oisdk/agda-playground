module Data.Set.Member where

open import Prelude hiding (⊥)
open import Data.Set.Definition
open import Data.Set.Eliminators
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Properties
open import Data.Sigma.Properties
open import HITs.PropositionalTruncation.Sugar

module  _ {a : Level} where
  memb-com-to : ∀ (x y x∈ys : Type a) → ∥ x ⊎ ∥ y ⊎ x∈ys ∥ ∥ → ∥ y ⊎ ∥ x ⊎ x∈ys ∥ ∥
  memb-com-to x y x∈ys t = t >>= (either′ (∣_∣ ∘ inr ∘ ∣_∣ ∘ inl) (_∥$∥_ (mapʳ (∣_∣ ∘ inr))) )

  memb-com : ∀ (x y x∈ys : Type a) → ∥ x ⊎ ∥ y ⊎ x∈ys ∥ ∥ ⇔ ∥ y ⊎ ∥ x ⊎ x∈ys ∥ ∥
  memb-com x y x∈ys .fun = memb-com-to x y x∈ys
  memb-com x y x∈ys .inv = memb-com-to y x x∈ys
  memb-com x y x∈ys .rightInv _ = squash _ _
  memb-com x y x∈ys .leftInv _ = squash _ _

  memb-dup-to : ∀ (x x∈ys : Type a) → ∥ x ⊎ ∥ x ⊎ x∈ys ∥ ∥ → ∥ x ⊎ x∈ys ∥
  memb-dup-to x x∈ys t = t >>= either (∣_∣ ∘ inl) id

  memb-dup : ∀ (x x∈ys : Type a) → ∥ x ⊎ ∥ x ⊎ x∈ys ∥ ∥ ⇔ ∥ x ⊎ x∈ys ∥
  memb-dup x x∈ys .fun = memb-dup-to x x∈ys
  memb-dup x x∈ys .inv = ∣_∣ ∘ inr
  memb-dup x x∈ys .rightInv _ = squash _ _
  memb-dup x x∈ys .leftInv _ = squash _ _

  open import Data.Empty.UniversePolymorphic {a}

  module _ {A : Type a} where

    ∈-alg-compute : A → Alg {A = A} λ _ → hProp a
    ∈-alg-compute x ∅                     = ⊥ , λ ()
    ∈-alg-compute x (y ∷ xs ⟨ x∈xs , _ ⟩) = ∥ (x ≡ y) ⊎ x∈xs ∥ , squash

    ∈-alg : A → ψ A (hProp a)
    ∈-alg x .fst = ∈-alg-compute x
    ∈-alg x .snd .c-trunc _ = isSetHProp
    ∈-alg x .snd .c-com y z xs (x∈xs , _) = Σ≡Prop (λ _ → isPropIsProp) (isoToPath (memb-com (x ≡ y) (x ≡ z) x∈xs))
    ∈-alg x .snd .c-dup y   xs (x∈xs , _) = Σ≡Prop (λ _ → isPropIsProp) (isoToPath (memb-dup (x ≡ y) x∈xs))

    _∈_ : A → 𝒦 A → Type a
    x ∈ xs = fst (⟦ ∈-alg x ⟧ xs)

    -- module _ (_≟_ : Discrete A) where

    --   open import Relation.Nullary.Decidable.Logic

    --   ∈?-alg : (x : A) → Ψ[ xs ⦂ 𝒦 A ] ↦ Dec (x ∈ xs)
    --   ∈?-alg x .fst ∅ = no λ ()
    --   ∈?-alg x .fst (y ∷ xs ⟨ x∈?xs ⟩) = disj (∣_∣ ∘ inl) (∣_∣ ∘ inr) {!!} (x ≟ y) x∈?xs
    --   ∈?-alg x .snd = {!!}

    --   _∈?_ : ∀ x xs → Dec (x ∈ xs)
    --   _∈?_ = {!!}
