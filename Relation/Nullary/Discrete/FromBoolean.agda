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
    ⟦yes sound x y
    ,no (λ p → subst (λ z → T (x ≡ᴮ z)) p (complete x))
    ⟧ (from-bool (x ≡ᴮ y))
