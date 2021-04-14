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

lb-pord : PartialOrder ⌈∙⌉ _
lb-pord .PartialOrder.preorder .Preorder._≤_ = _⌈≤⌉_
lb-pord .PartialOrder.preorder .Preorder.refl {⌈⊤⌉} = Poly.tt
lb-pord .PartialOrder.preorder .Preorder.refl {⌈ x ⌉} = <-refl
lb-pord .PartialOrder.preorder .Preorder.trans {x} {y} {⌈⊤⌉} x≤y y≤z = Poly.tt
lb-pord .PartialOrder.preorder .Preorder.trans {⌈ x ⌉} {⌈ y ⌉} {⌈ z ⌉} x≤y y≤z = ≤-trans x≤y y≤z
lb-pord .PartialOrder.antisym {⌈⊤⌉} {⌈⊤⌉} p q = refl
lb-pord .PartialOrder.antisym {⌈ x ⌉} {⌈ y ⌉} p q = cong ⌈_⌉ (antisym p q)

lb-sord : StrictPartialOrder ⌈∙⌉ _
StrictPreorder._<_   (StrictPartialOrder.strictPreorder lb-sord) = _⌈<⌉_
StrictPreorder.trans (StrictPartialOrder.strictPreorder lb-sord) {⌈ x ⌉} {⌈ y ⌉} {⌈⊤⌉} p q = Poly.tt
StrictPreorder.trans (StrictPartialOrder.strictPreorder lb-sord) {⌈ x ⌉} {⌈ y ⌉} {⌈ z ⌉} p q = <-trans p q
StrictPreorder.irrefl  (StrictPartialOrder.strictPreorder lb-sord) {⌈ x ⌉} = irrefl {x = x}
StrictPartialOrder.conn lb-sord {⌈⊤⌉} {⌈⊤⌉} p q = refl
StrictPartialOrder.conn lb-sord {⌈⊤⌉} {⌈ x ⌉} p q = ⊥-elim (q Poly.tt)
StrictPartialOrder.conn lb-sord {⌈ x ⌉} {⌈⊤⌉} p q = ⊥-elim (p Poly.tt)
StrictPartialOrder.conn lb-sord {⌈ x ⌉} {⌈ y ⌉} p q = cong ⌈_⌉ (conn p q)

lb-lt : ∀ x y → Dec (x ⌈<⌉ y)
lb-lt ⌈⊤⌉ y = no λ ()
lb-lt ⌈ x ⌉ ⌈⊤⌉ = yes Poly.tt
lb-lt ⌈ x ⌉ ⌈ y ⌉ = x <? y

lb-ord : TotalOrder ⌈∙⌉ _ _
TotalOrder.strictPartialOrder lb-ord = lb-sord
TotalOrder.partialOrder lb-ord = lb-pord
TotalOrder._<?_ lb-ord = lb-lt
TotalOrder.≰⇒> lb-ord {x} {⌈⊤⌉} p = ⊥-elim (p Poly.tt)
TotalOrder.≰⇒> lb-ord {⌈⊤⌉} {⌈ y ⌉} p = Poly.tt
TotalOrder.≰⇒> lb-ord {⌈ x ⌉} {⌈ y ⌉} p = ≰⇒> p
TotalOrder.≮⇒≥ lb-ord {⌈⊤⌉} {y} p = Poly.tt
TotalOrder.≮⇒≥ lb-ord {⌈ x ⌉} {⌈⊤⌉} p = ⊥-elim (p Poly.tt)
TotalOrder.≮⇒≥ lb-ord {⌈ x ⌉} {⌈ y ⌉} p = ≮⇒≥ p
