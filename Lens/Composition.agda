{-# OPTIONS --cubical --safe #-}

module Lens.Composition where

open import Prelude
open import Lens.Definition
open import Lens.Operators

infixr 9 _⋯_
_⋯_ : Lens A B → Lens B C → Lens A C
into (ab ⋯ bc) xs = ac
  where
  ab-xs : LensPart _ _
  ab-xs = into ab xs

  bc-ys : LensPart _ _
  bc-ys = into bc (get ab-xs)

  ac : LensPart _ _
  get ac = get bc-ys
  set ac v = set ab-xs (set bc-ys v)
get-set (ab ⋯ bc) s v = cong (getter bc) (get-set ab s _) ; bc .get-set (get (into ab s)) v
set-get (ab ⋯ bc) s = cong (setter ab s) (set-get bc (get (into ab s))) ; set-get ab s
set-set (ab ⋯ bc) s v₁ v₂ = set-set ab s _ _ ; cong (setter ab s) (cong (flip (setter bc) v₂) (get-set ab _ _) ; set-set bc _ _ _)
