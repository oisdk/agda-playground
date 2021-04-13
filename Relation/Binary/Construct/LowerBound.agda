{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary


module Relation.Binary.Construct.LowerBound {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open TotalOrder totalOrder renaming (refl to <-refl)
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

data ⌊∙⌋ : Type e where
  ⌊⊥⌋ : ⌊∙⌋
  ⌊_⌋ : E → ⌊∙⌋

⌊_⌋≤_ : E → ⌊∙⌋ → Type _
⌊ x ⌋≤ ⌊⊥⌋ = Poly.⊥
⌊ x ⌋≤ ⌊ y ⌋ = x ≤ y

_⌊≤⌋_ : ⌊∙⌋ → ⌊∙⌋ → Type _
⌊⊥⌋   ⌊≤⌋ y = Poly.⊤
⌊ x ⌋ ⌊≤⌋ y = ⌊ x ⌋≤ y

_<⌊_⌋ : ⌊∙⌋ → E → Type _
⌊⊥⌋   <⌊ y ⌋ = Poly.⊤
⌊ x ⌋ <⌊ y ⌋ = x < y

_⌊<⌋_ : ⌊∙⌋ → ⌊∙⌋ → Type _
_     ⌊<⌋ ⌊⊥⌋   = Poly.⊥
x     ⌊<⌋ ⌊ y ⌋ = x <⌊ y ⌋

lb-pord : PartialOrder ⌊∙⌋ _
Preorder._≤_   (PartialOrder.preorder lb-pord) = _⌊≤⌋_
Preorder.refl  (PartialOrder.preorder lb-pord) {⌊⊥⌋} = _
Preorder.refl  (PartialOrder.preorder lb-pord) {⌊ x ⌋} = <-refl
Preorder.trans (PartialOrder.preorder lb-pord) {⌊⊥⌋} {_} {_} p q = _
Preorder.trans (PartialOrder.preorder lb-pord) {⌊ x ⌋} {⌊ y ⌋} {⌊ z ⌋} p q = ≤-trans p q
PartialOrder.antisym lb-pord {⌊⊥⌋} {⌊⊥⌋} p q = refl
PartialOrder.antisym lb-pord {⌊ x ⌋} {⌊ x₁ ⌋} p q = cong ⌊_⌋ (antisym p q)



lb-sord : StrictPartialOrder ⌊∙⌋ _
StrictPreorder._<_   (StrictPartialOrder.strictPreorder lb-sord) = _⌊<⌋_
StrictPreorder.trans (StrictPartialOrder.strictPreorder lb-sord) {⌊⊥⌋} {⌊⊥⌋} {⌊⊥⌋} p q = q
StrictPreorder.trans (StrictPartialOrder.strictPreorder lb-sord) {⌊⊥⌋} {⌊⊥⌋} {⌊ x ⌋} p q = q
StrictPreorder.trans (StrictPartialOrder.strictPreorder lb-sord) {⌊⊥⌋} {⌊ x ⌋} {⌊ x₁ ⌋} p q = p
StrictPreorder.trans (StrictPartialOrder.strictPreorder lb-sord) {⌊ x ⌋} {⌊ x₁ ⌋} {⌊ x₂ ⌋} p q = <-trans p q
StrictPreorder.irrefl  (StrictPartialOrder.strictPreorder lb-sord) {⌊ x ⌋} = irrefl {x = x}
StrictPartialOrder.conn  lb-sord {⌊⊥⌋} {⌊⊥⌋} p q = refl
StrictPartialOrder.conn  lb-sord {⌊⊥⌋} {⌊ x ⌋} p q = ⊥-elim (p _)
StrictPartialOrder.conn  lb-sord {⌊ x ⌋} {⌊⊥⌋} p q = ⊥-elim (q _)
StrictPartialOrder.conn  lb-sord {⌊ x ⌋} {⌊ x₁ ⌋} p q = cong ⌊_⌋ (conn p q)

lb-lt : ∀ x y → Dec (x ⌊<⌋ y)
lb-lt x ⌊⊥⌋ = no (λ ())
lb-lt ⌊⊥⌋ ⌊ y ⌋ = yes Poly.tt
lb-lt ⌊ x ⌋ ⌊ y ⌋ = x <? y

lb-ord : TotalOrder ⌊∙⌋ _ _
TotalOrder.strictPartialOrder lb-ord = lb-sord
TotalOrder.partialOrder lb-ord = lb-pord
TotalOrder._<?_ lb-ord = lb-lt
TotalOrder.≰⇒> lb-ord {⌊⊥⌋} {⌊⊥⌋} p = ⊥-elim (p _)
TotalOrder.≰⇒> lb-ord {⌊⊥⌋} {⌊ x ⌋} p = ⊥-elim (p _ )
TotalOrder.≰⇒> lb-ord {⌊ x ⌋} {⌊⊥⌋} p = _
TotalOrder.≰⇒> lb-ord {⌊ x ⌋} {⌊ x₁ ⌋} p = ≰⇒> p
TotalOrder.≮⇒≥ lb-ord {x} {⌊⊥⌋} p = _
TotalOrder.≮⇒≥ lb-ord {⌊⊥⌋} {⌊ y ⌋} p = ⊥-elim (p _)
TotalOrder.≮⇒≥ lb-ord {⌊ x ⌋} {⌊ y ⌋} p = ≮⇒≥ p
