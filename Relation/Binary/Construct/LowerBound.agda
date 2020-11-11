{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary


module Relation.Binary.Construct.LowerBound {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open TotalOrder totalOrder renaming (refl to ≤-refl)
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

data ⌊∙⌋ : Type e where
  ⌊⊥⌋ : ⌊∙⌋
  ⌊_⌋ : E → ⌊∙⌋

_≤⌊_⌋ : ⌊∙⌋ → E → Type _
⌊⊥⌋   ≤⌊ y ⌋ = Poly.⊤
⌊ x ⌋ ≤⌊ y ⌋ = x ≤ y

_⌊≤⌋_ : ⌊∙⌋ → ⌊∙⌋ → Type _
x     ⌊≤⌋ ⌊ y ⌋ = x ≤⌊ y ⌋
⌊⊥⌋   ⌊≤⌋ ⌊⊥⌋   = Poly.⊤
⌊ x ⌋ ⌊≤⌋ ⌊⊥⌋   = Poly.⊥

lb-pord : PartialOrder ⌊∙⌋ _
PartialOrder._≤_ lb-pord = _⌊≤⌋_
PartialOrder.refl lb-pord {⌊⊥⌋} = Poly.tt
PartialOrder.refl lb-pord {⌊ x ⌋} = ≤-refl
PartialOrder.antisym lb-pord {⌊⊥⌋} {⌊⊥⌋} x≤y y≤x _ = ⌊⊥⌋
PartialOrder.antisym lb-pord {⌊ x ⌋} {⌊ x₁ ⌋} x≤y y≤x i = ⌊ antisym x≤y y≤x i ⌋
PartialOrder.trans lb-pord {⌊⊥⌋} {⌊⊥⌋} {⌊⊥⌋} x≤y y≤z = Poly.tt
PartialOrder.trans lb-pord {⌊⊥⌋} {⌊⊥⌋} {⌊ x ⌋} x≤y y≤z = Poly.tt
PartialOrder.trans lb-pord {⌊⊥⌋} {⌊ x ⌋} {⌊ x₁ ⌋} x≤y y≤z = Poly.tt
PartialOrder.trans lb-pord {⌊ x ⌋} {⌊ x₁ ⌋} {⌊ x₂ ⌋} x≤y y≤z = ≤-trans x≤y y≤z

lb-lte : Total _⌊≤⌋_
lb-lte ⌊⊥⌋ ⌊⊥⌋ = inl Poly.tt
lb-lte ⌊⊥⌋ ⌊ x ⌋ = inl Poly.tt
lb-lte ⌊ x ⌋ ⌊⊥⌋ = inr Poly.tt
lb-lte ⌊ x ⌋ ⌊ y ⌋ = x ≤? y

lb-ord : TotalOrder ⌊∙⌋ _ _
lb-ord = fromPartialOrder lb-pord lb-lte
