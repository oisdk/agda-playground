{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Nat.Order where

open import Prelude
open import Data.Nat.Properties
open import Relation.Binary

<-trans : Transitive _<_
<-trans {zero} {suc y} {suc z} x<y y<z = tt
<-trans {suc x} {suc y} {suc z} x<y y<z = <-trans {x} {y} {z} x<y y<z

<-asym : Asymmetric _<_
<-asym {suc x} {suc y} x<y y<x = <-asym {x} {y} x<y y<x

<-irrefl : Irreflexive _<_
<-irrefl {suc x} = <-irrefl {x = x}

<-conn : Connected _<_
<-conn {zero} {zero} x≮y y≮x = refl
<-conn {zero} {suc y} x≮y y≮x = ⊥-elim (x≮y tt)
<-conn {suc x} {zero} x≮y y≮x = ⊥-elim (y≮x tt)
<-conn {suc x} {suc y} x≮y y≮x = cong suc (<-conn x≮y y≮x)

≤-antisym : Antisymmetric _≤_
≤-antisym {zero} {zero} x≤y y≤x = refl
≤-antisym {suc x} {suc y} x≤y y≤x = cong suc (≤-antisym x≤y y≤x)

ℕ-≰⇒> : ∀ x y → ¬ (x ≤ y) → y < x
ℕ-≰⇒> x y x≰y with y <ᴮ x
... | false = x≰y tt
... | true = tt

ℕ-≮⇒≥ : ∀ x y → ¬ (x < y) → y ≤ x
ℕ-≮⇒≥ x y x≮y with x <ᴮ y
... | false = tt
... | true = x≮y tt

totalOrder : TotalOrder ℕ ℓzero ℓzero
totalOrder .TotalOrder.strictPartialOrder .StrictPartialOrder.strictPreorder .StrictPreorder._<_ = _<_
totalOrder .TotalOrder.strictPartialOrder .StrictPartialOrder.strictPreorder .StrictPreorder.trans {x} {y} {z} = <-trans {x} {y} {z}
totalOrder .TotalOrder.strictPartialOrder .StrictPartialOrder.strictPreorder .StrictPreorder.irrefl {x} = <-irrefl {x = x}
totalOrder .TotalOrder.strictPartialOrder .StrictPartialOrder.conn = <-conn
totalOrder .TotalOrder.partialOrder .PartialOrder.preorder .Preorder._≤_ = _≤_
totalOrder .TotalOrder.partialOrder .PartialOrder.preorder .Preorder.refl {x} = ≤-refl x
totalOrder .TotalOrder.partialOrder .PartialOrder.preorder .Preorder.trans {x} {y} {z} = ≤-trans x y z
totalOrder .TotalOrder.partialOrder .PartialOrder.antisym = ≤-antisym
totalOrder .TotalOrder._<?_ x y = T? (x <ᴮ y)
totalOrder .TotalOrder.≰⇒> {x} {y} = ℕ-≰⇒> x y
totalOrder .TotalOrder.≮⇒≥ {x} {y} = ℕ-≮⇒≥ x y
