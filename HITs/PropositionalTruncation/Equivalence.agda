{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation.Equivalence where

open import Prelude
open import Relation.Binary
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

trunc-equivalence : ∀ {a} {A : Type a} → Equivalence A a → Equivalence A a
trunc-equivalence e .Equivalence._≋_ x y = ∥ Equivalence._≋_ e x y ∥
trunc-equivalence e .Equivalence.sym = _∥$∥_ (Equivalence.sym e)
trunc-equivalence e .Equivalence.refl = ∣ Equivalence.refl e ∣
trunc-equivalence e .Equivalence.trans xy yz = ⦇ (Equivalence.trans e) xy yz ⦈
