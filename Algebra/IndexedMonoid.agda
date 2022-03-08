open import Algebra
open import Prelude

module Algebra.IndexedMonoid {ℓ₁ ℓ₂} (mon : Monoid ℓ₁) (U : Monoid.𝑆 mon → Type ℓ₂) where

open Monoid mon

private
  variable x y z : 𝑆


record MonoidCongruent : Type (ℓ₁ ℓ⊔ ℓ₂) where
  field
    ⓔ   : U ε
    _⊙_ : U x → U y → U (x ∙ y)
  
    ⓔ⊙ : (xs : U x) → ⓔ ⊙ xs ≡[ i ≔ U (ε∙ x i) ]≡ xs
    ⊙ⓔ : (xs : U x) → xs ⊙ ⓔ ≡[ i ≔ U (∙ε x i) ]≡ xs
    ⊙-assoc : (xs : U x) (ys : U y) (zs : U z) → (xs ⊙ ys) ⊙ zs ≡[ i ≔ U (assoc x y z i) ]≡ xs ⊙ (ys ⊙ zs)

open import Data.Sigma.Properties

record ComonoidCongruent : Type (ℓ₁ ℓ⊔ ℓ₂) where
  field
    ⊙ᵒ : U (x ∙ y) → U x × U y

  ⊙ˡ : U (x ∙ y) → U x
  ⊙ˡ = fst ∘ ⊙ᵒ

  ⊙ʳ : U (x ∙ y) → U y
  ⊙ʳ = snd ∘ ⊙ᵒ
  
  field
    ⓔ⊙ʳ : (xs : U (ε ∙ x)) → xs ≡[ i ≔ U (ε∙ x i) ]≡ ⊙ʳ xs
    ⊙ⓔˡ : (xs : U (x ∙ ε)) → xs ≡[ i ≔ U (∙ε x i) ]≡ ⊙ˡ xs
    ⊙ᵒ-assoc : reassoc .fun ∘ map₁ ⊙ᵒ ∘ ⊙ᵒ ≡[ i ≔ (U (assoc x y z i) → U x × U y × U z) ]≡ map₂ ⊙ᵒ ∘ ⊙ᵒ
