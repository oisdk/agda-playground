{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary


module Relation.Binary.Construct.LowerBound {e} {E : Type e} {r} (totalOrder : TotalOrder E r) where

open TotalOrder totalOrder renaming (refl to ≤-refl)
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

data ⌊∙⌋ : Type e where
  ⌊⊥⌋ : ⌊∙⌋
  ⌊_⌋ : E → ⌊∙⌋

_≤⌊_⌋ : ⌊∙⌋ → E → Type r
⌊⊥⌋   ≤⌊ y ⌋ = Poly.⊤
⌊ x ⌋ ≤⌊ y ⌋ = x ≤ y

_⌊≤⌋_ : ⌊∙⌋ → ⌊∙⌋ → Type r
x     ⌊≤⌋ ⌊ y ⌋ = x ≤⌊ y ⌋
⌊⊥⌋   ⌊≤⌋ ⌊⊥⌋   = Poly.⊤
⌊ x ⌋ ⌊≤⌋ ⌊⊥⌋   = Poly.⊥

lb-ord : TotalOrder ⌊∙⌋ r
PartialOrder._≤_ (TotalOrder.partialOrder lb-ord) = _⌊≤⌋_
PartialOrder.refl (partialOrder lb-ord) {⌊⊥⌋} = Poly.tt
PartialOrder.refl (partialOrder lb-ord) {⌊ x ⌋} = ≤-refl
PartialOrder.antisym (TotalOrder.partialOrder lb-ord) {⌊⊥⌋} {⌊⊥⌋} x≤y y≤x _ = ⌊⊥⌋
PartialOrder.antisym (TotalOrder.partialOrder lb-ord) {⌊ x ⌋} {⌊ x₁ ⌋} x≤y y≤x i = ⌊ antisym x≤y y≤x i ⌋
PartialOrder.trans (TotalOrder.partialOrder lb-ord) {⌊⊥⌋} {⌊⊥⌋} {⌊⊥⌋} x≤y y≤z = Poly.tt
PartialOrder.trans (TotalOrder.partialOrder lb-ord) {⌊⊥⌋} {⌊⊥⌋} {⌊ x ⌋} x≤y y≤z = Poly.tt
PartialOrder.trans (TotalOrder.partialOrder lb-ord) {⌊⊥⌋} {⌊ x ⌋} {⌊ x₁ ⌋} x≤y y≤z = Poly.tt
PartialOrder.trans (TotalOrder.partialOrder lb-ord) {⌊ x ⌋} {⌊ x₁ ⌋} {⌊ x₂ ⌋} x≤y y≤z = trans x≤y y≤z
TotalOrder._≤?_ lb-ord ⌊⊥⌋ ⌊⊥⌋ = inl Poly.tt
TotalOrder._≤?_ lb-ord ⌊ x ⌋ ⌊⊥⌋ = inr Poly.tt
TotalOrder._≤?_ lb-ord ⌊⊥⌋ ⌊ x₁ ⌋ = inl Poly.tt
TotalOrder._≤?_ lb-ord ⌊ x ⌋ ⌊ y ⌋ = x ≤? y
