{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary

module Relation.Binary.Construct.Decision
  {a ℓ₁ ℓ₂} {A : Type a}
  (ord : TotalOrder A ℓ₁ ℓ₂)
  where

open TotalOrder ord renaming (refl to ≤-refl)

_<′_ : A → A → Type₀
x <′ y = T (does (x <? y))

_≤′_ : A → A → Type₀
x ≤′ y = T (not (does (y <? x)))


witness-< : ∀ {x y} → x <′ y → x < y
witness-< {x} {y} p with x <? y
witness-< {x} {y} p | yes q = q

witness-≤ : ∀ {x y} → x ≤′ y → x ≤ y
witness-≤ {x} {y} p with y <? x
witness-≤ {x} {y} p | no q = ≮⇒≥ q

compute-< : ∀ {x y} → x < y → x <′ y
compute-< {x} {y} p with x <? y
compute-< {x} {y} p | yes q = tt
compute-< {x} {y} p | no ¬p = ⊥-elim (¬p p)

compute-≤ : ∀ {x y} → x ≤ y → x ≤′ y
compute-≤ {x} {y} ¬p with y <? x
compute-≤ {x} {y} ¬p | yes p = ⊥-elim (<⇒≱ p ¬p)
compute-≤ {x} {y} ¬p | no  _ = tt


≰⇒>′ : ∀ {x y} → ¬ (x ≤′ y) → y <′ x
≰⇒>′ {x} {y} p with y <? x
≰⇒>′ {x} {y} p | no  _ = p tt
≰⇒>′ {x} {y} p | yes _ = tt

≮⇒≥′ : ∀ {x y} → ¬ (x <′ y) → y ≤′ x
≮⇒≥′ {x} {y} p with x <? y
≮⇒≥′ {x} {y} p | no  _ = tt
≮⇒≥′ {x} {y} p | yes _ = p tt

dec-ord : TotalOrder A ℓzero ℓzero
StrictPreorder._<_    (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder dec-ord)) = _<′_
StrictPreorder.trans  (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder dec-ord)) p q = compute-< (<-trans (witness-< p) (witness-< q))
StrictPreorder.irrefl (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder dec-ord)) p = irrefl (witness-< p)
StrictPartialOrder.conn (TotalOrder.strictPartialOrder dec-ord) p q = conn (p ∘ compute-<) (q ∘ compute-<)
Preorder._≤_  (PartialOrder.preorder (TotalOrder.partialOrder dec-ord)) = _≤′_
Preorder.refl (PartialOrder.preorder (TotalOrder.partialOrder dec-ord)) = compute-≤ ≤-refl
PartialOrder.antisym (TotalOrder.partialOrder dec-ord) p q = antisym (witness-≤ p) (witness-≤ q)
Preorder.trans (PartialOrder.preorder (TotalOrder.partialOrder dec-ord)) p q = compute-≤ (≤-trans (witness-≤ p) (witness-≤ q))
TotalOrder._<?_ dec-ord x y = ⟦yes compute-< ,no  witness-< ⟧ (x <? y)
TotalOrder.≰⇒> dec-ord = ≰⇒>′
TotalOrder.≮⇒≥ dec-ord = ≮⇒≥′
