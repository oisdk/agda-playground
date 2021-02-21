{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary
open import Function.Injective

module Relation.Binary.Construct.On
  {a b ℓ₁ ℓ₂} {A : Type a} {B : Type b}
  (f : A → B) (f-inj : Injective f)
  (ord : TotalOrder B ℓ₁ ℓ₂)
  where

open TotalOrder ord renaming (refl to ≤-refl)

_<′_ : A → A → Type _
x <′ y = f x < f y

_≤′_ : A → A → Type _
x ≤′ y = f x ≤ f y

on-ord : TotalOrder A ℓ₁ ℓ₂
StrictPartialOrder._<_ (TotalOrder.strictPartialOrder on-ord) = _<′_
StrictPartialOrder.trans (TotalOrder.strictPartialOrder on-ord) = <-trans
StrictPartialOrder.asym (TotalOrder.strictPartialOrder on-ord) = asym
StrictPartialOrder.conn (TotalOrder.strictPartialOrder on-ord) p q = f-inj _ _ (conn p q)
PartialOrder._≤_ (TotalOrder.partialOrder on-ord) = _≤′_
PartialOrder.refl (TotalOrder.partialOrder on-ord) = ≤-refl
PartialOrder.antisym (TotalOrder.partialOrder on-ord) p q = f-inj _ _ (antisym p q)
PartialOrder.trans (TotalOrder.partialOrder on-ord) = ≤-trans
TotalOrder._<?_ on-ord x y = f x <? f y
TotalOrder.≰⇒> on-ord = ≰⇒>
TotalOrder.≮⇒≥ on-ord = ≮⇒≥
