{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Discrete.FromBoolean where

open import Prelude
open import Relation.Nullary.Discrete

module _ {a} {A : Type a}
             (_≡ᴮ_ : A → A → Bool)
             (sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y)
             (complete : ∀ x → T (x ≡ᴮ x))
  where

  from-bool-eq : Discrete A
  from-bool-eq x y =
    iff-dec (sound x y iff flip (subst (λ z → T (x ≡ᴮ z))) (complete x)) (T? (x ≡ᴮ y))
