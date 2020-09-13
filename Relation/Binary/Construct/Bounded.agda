{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Relation.Binary.Construct.Bounded {e} {E : Type e} {r} (totalOrder : TotalOrder E r) where

open TotalOrder totalOrder renaming (refl to ≤-refl)
import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

data [∙] : Type e where
  [⊥] [⊤] : [∙]
  [_] : E → [∙]

_≤[_] : [∙] → E → Type r
[⊤]   ≤[ _ ] = Poly.⊥
[⊥]   ≤[ y ] = Poly.⊤
[ x ] ≤[ y ] = x ≤ y

_[≤]_ : [∙] → [∙] → Type r
[⊥]   [≤] _     = Poly.⊤
_     [≤] [⊤]   = Poly.⊤
[⊤]   [≤] _     = Poly.⊥
_     [≤] [⊥]   = Poly.⊥
[ x ] [≤] [ y ] = x ≤ y

b-ord : TotalOrder [∙] r
b-ord .TotalOrder.partialOrder .PartialOrder._≤_ = _[≤]_
b-ord .TotalOrder.partialOrder .PartialOrder.refl {[⊥]} = Poly.tt
b-ord .TotalOrder.partialOrder .PartialOrder.refl {[⊤]} = Poly.tt
b-ord .TotalOrder.partialOrder .PartialOrder.refl {[ x ]} = ≤-refl
b-ord .TotalOrder.partialOrder .PartialOrder.antisym {[⊥]} {[⊥]} x≤y y≤x i = [⊥]
b-ord .TotalOrder.partialOrder .PartialOrder.antisym {[⊤]} {[⊤]} x≤y y≤x i = [⊤]
b-ord .TotalOrder.partialOrder .PartialOrder.antisym {[ x ]} {[ y ]} x≤y y≤x i = [ antisym x≤y y≤x i ]
b-ord .TotalOrder.partialOrder .PartialOrder.trans {[⊥]} {y} {z} x≤y y≤z = Poly.tt
b-ord .TotalOrder.partialOrder .PartialOrder.trans {[⊤]} {[⊤]} {[⊤]} x≤y y≤z = Poly.tt
b-ord .TotalOrder.partialOrder .PartialOrder.trans {[ x ]} {[⊤]} {[⊤]} x≤y y≤z = Poly.tt
b-ord .TotalOrder.partialOrder .PartialOrder.trans {[ x ]} {[ y ]} {[⊤]} x≤y y≤z = Poly.tt
b-ord .TotalOrder.partialOrder .PartialOrder.trans {[ x ]} {[ y ]} {[ z ]} x≤y y≤z = trans x≤y y≤z
b-ord .TotalOrder._≤?_ [⊥] y = inl Poly.tt
b-ord .TotalOrder._≤?_ [⊤] [⊥] = inr Poly.tt
b-ord .TotalOrder._≤?_ [⊤] [⊤] = inr Poly.tt
b-ord .TotalOrder._≤?_ [⊤] [ y ] = inr Poly.tt
b-ord .TotalOrder._≤?_ [ x ] [⊥] = inr Poly.tt
b-ord .TotalOrder._≤?_ [ x ] [⊤] = inl Poly.tt
b-ord .TotalOrder._≤?_ [ x ] [ y ] = x ≤? y
