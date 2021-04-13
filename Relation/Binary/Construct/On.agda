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
StrictPreorder._<_   (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder on-ord)) = _<′_
StrictPreorder.trans (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder on-ord)) = <-trans
StrictPreorder.irrefl  (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder on-ord)) = irrefl
StrictPartialOrder.conn (TotalOrder.strictPartialOrder on-ord) p q = f-inj _ _ (conn p q)
Preorder._≤_   (PartialOrder.preorder (TotalOrder.partialOrder on-ord)) = _≤′_
Preorder.refl  (PartialOrder.preorder (TotalOrder.partialOrder on-ord)) = ≤-refl
Preorder.trans (PartialOrder.preorder (TotalOrder.partialOrder on-ord)) = ≤-trans
PartialOrder.antisym (TotalOrder.partialOrder on-ord) p q = f-inj _ _ (antisym p q)
TotalOrder._<?_ on-ord x y = f x <? f y
TotalOrder.≰⇒> on-ord = ≰⇒>
TotalOrder.≮⇒≥ on-ord = ≮⇒≥
