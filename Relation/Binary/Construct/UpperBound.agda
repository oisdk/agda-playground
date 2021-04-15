{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary


module Relation.Binary.Construct.UpperBound {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open TotalOrder totalOrder renaming (refl to <-refl)
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

data ⌈∙⌉ : Type e where
  ⌈⊤⌉ : ⌈∙⌉
  ⌈_⌉ : E → ⌈∙⌉

_≤⌈_⌉ : ⌈∙⌉ → E → Type _
⌈⊤⌉   ≤⌈ y ⌉ = Poly.⊥
⌈ x ⌉ ≤⌈ y ⌉ = x ≤ y

_⌈≤⌉_ : ⌈∙⌉ → ⌈∙⌉ → Type _
x ⌈≤⌉ ⌈⊤⌉   = Poly.⊤
x ⌈≤⌉ ⌈ y ⌉ = x ≤⌈ y ⌉

⌈_⌉<_ : E → ⌈∙⌉ → Type _
⌈ x ⌉< ⌈⊤⌉   = Poly.⊤
⌈ x ⌉< ⌈ y ⌉ = x < y

_⌈<⌉_ : ⌈∙⌉ → ⌈∙⌉ → Type _
⌈⊤⌉   ⌈<⌉ _ = Poly.⊥
⌈ x ⌉ ⌈<⌉ y = ⌈ x ⌉< y

ub-pord : PartialOrder ⌈∙⌉ _
ub-pord .PartialOrder.preorder .Preorder._≤_ = _⌈≤⌉_
ub-pord .PartialOrder.preorder .Preorder.refl {⌈⊤⌉} = Poly.tt
ub-pord .PartialOrder.preorder .Preorder.refl {⌈ x ⌉} = <-refl
ub-pord .PartialOrder.preorder .Preorder.trans {x} {y} {⌈⊤⌉} x≤y y≤z = Poly.tt
ub-pord .PartialOrder.preorder .Preorder.trans {⌈ x ⌉} {⌈ y ⌉} {⌈ z ⌉} x≤y y≤z = ≤-trans x≤y y≤z
ub-pord .PartialOrder.antisym {⌈⊤⌉} {⌈⊤⌉} p q = refl
ub-pord .PartialOrder.antisym {⌈ x ⌉} {⌈ y ⌉} p q = cong ⌈_⌉ (antisym p q)

ub-sord : StrictPartialOrder ⌈∙⌉ _
StrictPreorder._<_   (StrictPartialOrder.strictPreorder ub-sord) = _⌈<⌉_
StrictPreorder.trans (StrictPartialOrder.strictPreorder ub-sord) {⌈ x ⌉} {⌈ y ⌉} {⌈⊤⌉} p q = Poly.tt
StrictPreorder.trans (StrictPartialOrder.strictPreorder ub-sord) {⌈ x ⌉} {⌈ y ⌉} {⌈ z ⌉} p q = <-trans p q
StrictPreorder.irrefl  (StrictPartialOrder.strictPreorder ub-sord) {⌈ x ⌉} = irrefl {x = x}
StrictPartialOrder.conn ub-sord {⌈⊤⌉} {⌈⊤⌉} p q = refl
StrictPartialOrder.conn ub-sord {⌈⊤⌉} {⌈ x ⌉} p q = ⊥-elim (q Poly.tt)
StrictPartialOrder.conn ub-sord {⌈ x ⌉} {⌈⊤⌉} p q = ⊥-elim (p Poly.tt)
StrictPartialOrder.conn ub-sord {⌈ x ⌉} {⌈ y ⌉} p q = cong ⌈_⌉ (conn p q)

ub-lt : ∀ x y → Dec (x ⌈<⌉ y)
ub-lt ⌈⊤⌉ y = no λ ()
ub-lt ⌈ x ⌉ ⌈⊤⌉ = yes Poly.tt
ub-lt ⌈ x ⌉ ⌈ y ⌉ = x <? y

ub-ord : TotalOrder ⌈∙⌉ _ _
TotalOrder.strictPartialOrder ub-ord = ub-sord
TotalOrder.partialOrder ub-ord = ub-pord
TotalOrder._<?_ ub-ord = ub-lt
TotalOrder.≰⇒> ub-ord {x} {⌈⊤⌉} p = ⊥-elim (p Poly.tt)
TotalOrder.≰⇒> ub-ord {⌈⊤⌉} {⌈ y ⌉} p = Poly.tt
TotalOrder.≰⇒> ub-ord {⌈ x ⌉} {⌈ y ⌉} p = ≰⇒> p
TotalOrder.≮⇒≥ ub-ord {⌈⊤⌉} {y} p = Poly.tt
TotalOrder.≮⇒≥ ub-ord {⌈ x ⌉} {⌈⊤⌉} p = ⊥-elim (p Poly.tt)
TotalOrder.≮⇒≥ ub-ord {⌈ x ⌉} {⌈ y ⌉} p = ≮⇒≥ p
