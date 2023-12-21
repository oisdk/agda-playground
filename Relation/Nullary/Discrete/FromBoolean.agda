{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Discrete.FromBoolean where

open import Prelude
open import Relation.Nullary.Discrete

record EqAlg (A : Type a) : Type a where
  field
    _≡ᴮ_ : A → A → Bool
    sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y
    complete : ∀ x → T (x ≡ᴮ x)

  from-bool-eq : Discrete A
  from-bool-eq x y =
    dec-bool
      (x ≡ᴮ y)
      (sound x y)
      (λ x≡y → subst (λ y → T (x ≡ᴮ y)) x≡y (complete x))
open EqAlg using (from-bool-eq) public
