{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Relation.Binary.Construct.Bounded {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open TotalOrder totalOrder renaming (refl to ≤-refl)
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

data [∙] : Type e where
  [⊥] [⊤] : [∙]
  [_] : E → [∙]

_[≤]_ : [∙] → [∙] → Type _
[⊥]   [≤] _     = Poly.⊤
_     [≤] [⊤]   = Poly.⊤
[⊤]   [≤] _     = Poly.⊥
_     [≤] [⊥]   = Poly.⊥
[ x ] [≤] [ y ] = x ≤ y

_[<]_ : [∙] → [∙] → Type _
[⊤]   [<] _     = Poly.⊥
_     [<] [⊥]   = Poly.⊥
[⊥]   [<] _     = Poly.⊤
_     [<] [⊤]   = Poly.⊤
[ x ] [<] [ y ] = x < y

b-pord : PartialOrder [∙] _
b-pord .PartialOrder.preorder .Preorder._≤_ = _[≤]_
b-pord .PartialOrder.preorder .Preorder.refl {[⊥]} = Poly.tt
b-pord .PartialOrder.preorder .Preorder.refl {[⊤]} = Poly.tt
b-pord .PartialOrder.preorder .Preorder.refl {[ x ]} = ≤-refl
b-pord .PartialOrder.preorder .Preorder.trans {[⊥]} {y} {z} x≤y y≤z = Poly.tt
b-pord .PartialOrder.preorder .Preorder.trans {[⊤]} {[⊤]} {[⊤]} x≤y y≤z = Poly.tt
b-pord .PartialOrder.preorder .Preorder.trans {[ x ]} {[⊤]} {[⊤]} x≤y y≤z = Poly.tt
b-pord .PartialOrder.preorder .Preorder.trans {[ x ]} {[ y ]} {[⊤]} x≤y y≤z = Poly.tt
b-pord .PartialOrder.preorder .Preorder.trans {[ x ]} {[ y ]} {[ z ]} x≤y y≤z = ≤-trans x≤y y≤z
b-pord .PartialOrder.antisym {[⊥]} {[⊥]} x≤y y≤x i = [⊥]
b-pord .PartialOrder.antisym {[⊤]} {[⊤]} x≤y y≤x i = [⊤]
b-pord .PartialOrder.antisym {[ x ]} {[ y ]} x≤y y≤x i = [ antisym x≤y y≤x i ]

b-sord : StrictPartialOrder [∙] _
b-sord .StrictPartialOrder._<_ = _[<]_
b-sord .StrictPartialOrder.trans {[⊥]} {[ x ]} {[⊤]} x<y y<z = Poly.tt
b-sord .StrictPartialOrder.trans {[⊥]} {[ x ]} {[ x₁ ]} x<y y<z = Poly.tt
b-sord .StrictPartialOrder.trans {[ x ]} {[ x₁ ]} {[⊤]} x<y y<z = Poly.tt
b-sord .StrictPartialOrder.trans {[ x ]} {[ x₁ ]} {[ x₂ ]} x<y y<z = <-trans x<y y<z
b-sord .StrictPartialOrder.asym {[⊥]} {[⊤]} x<y ()
b-sord .StrictPartialOrder.asym {[⊥]} {[ x ]} x<y ()
b-sord .StrictPartialOrder.asym {[ x ]} {[⊤]} x<y ()
b-sord .StrictPartialOrder.asym {[ x ]} {[ x₁ ]} x<y = asym x<y
b-sord .StrictPartialOrder.conn {[⊥]} {[⊥]} x≮y y≮x = refl
b-sord .StrictPartialOrder.conn {[⊥]} {[⊤]} x≮y y≮x = ⊥-elim (x≮y Poly.tt)
b-sord .StrictPartialOrder.conn {[⊥]} {[ x ]} x≮y y≮x = ⊥-elim (x≮y Poly.tt)
b-sord .StrictPartialOrder.conn {[⊤]} {[⊥]} x≮y y≮x = ⊥-elim (y≮x Poly.tt)
b-sord .StrictPartialOrder.conn {[⊤]} {[⊤]} x≮y y≮x = refl
b-sord .StrictPartialOrder.conn {[⊤]} {[ x ]} x≮y y≮x = ⊥-elim (y≮x Poly.tt)
b-sord .StrictPartialOrder.conn {[ x ]} {[⊥]} x≮y y≮x = ⊥-elim (y≮x Poly.tt)
b-sord .StrictPartialOrder.conn {[ x ]} {[⊤]} x≮y y≮x = ⊥-elim (x≮y Poly.tt)
b-sord .StrictPartialOrder.conn {[ x ]} {[ x₁ ]} x≮y y≮x = cong [_] (conn x≮y y≮x)

b-ord : TotalOrder [∙] _ _
b-ord .TotalOrder.strictPartialOrder = b-sord
b-ord .TotalOrder.partialOrder = b-pord
b-ord .TotalOrder._<?_ [⊥] [⊥] = no λ ()
b-ord .TotalOrder._<?_ [⊥] [⊤] = yes _
b-ord .TotalOrder._<?_ [⊥] [ y ] = yes _
b-ord .TotalOrder._<?_ [⊤] [⊥] = no λ ()
b-ord .TotalOrder._<?_ [⊤] [⊤] = no λ ()
b-ord .TotalOrder._<?_ [⊤] [ y ] = no λ ()
b-ord .TotalOrder._<?_ [ x ] [⊥] = no λ ()
b-ord .TotalOrder._<?_ [ x ] [⊤] = yes _
b-ord .TotalOrder._<?_ [ x ] [ y ] = x <? y
b-ord .TotalOrder.≰⇒> {[⊥]} {y} x≰y = ⊥-elim (x≰y Poly.tt)
b-ord .TotalOrder.≰⇒> {[⊤]} {[⊥]} x≰y = Poly.tt
b-ord .TotalOrder.≰⇒> {[⊤]} {[⊤]} x≰y = ⊥-elim (x≰y Poly.tt)
b-ord .TotalOrder.≰⇒> {[⊤]} {[ x ]} x≰y = Poly.tt
b-ord .TotalOrder.≰⇒> {[ x ]} {[⊥]} x≰y = Poly.tt
b-ord .TotalOrder.≰⇒> {[ x ]} {[⊤]} x≰y = ⊥-elim (x≰y Poly.tt)
b-ord .TotalOrder.≰⇒> {[ x ]} {[ x₁ ]} x≰y = ≰⇒> x≰y
b-ord .TotalOrder.≮⇒≥ {x} {[⊥]} x≮y = Poly.tt
b-ord .TotalOrder.≮⇒≥ {[⊥]} {[⊤]} x≮y = ⊥-elim (x≮y Poly.tt)
b-ord .TotalOrder.≮⇒≥ {[⊤]} {[⊤]} x≮y = Poly.tt
b-ord .TotalOrder.≮⇒≥ {[ x ]} {[⊤]} x≮y = ⊥-elim (x≮y Poly.tt)
b-ord .TotalOrder.≮⇒≥ {[⊥]} {[ x₁ ]} x≮y = ⊥-elim (x≮y Poly.tt)
b-ord .TotalOrder.≮⇒≥ {[⊤]} {[ x₁ ]} x≮y = Poly.tt
b-ord .TotalOrder.≮⇒≥ {[ x ]} {[ y ]} x≮y = ≮⇒≥ x≮y
