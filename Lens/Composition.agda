{-# OPTIONS --cubical --safe #-}

module Lens.Composition where

open import Prelude
open import Lens.Definition
open import Lens.Operators

infixr 9 _⋯_
_⋯_ : Lens A B → Lens B C → Lens A C
fst (ab ⋯ bc) xs = ac
  where
  ab-xs : LensPart _ _
  ab-xs = fst ab xs

  bc-ys : LensPart _ _
  bc-ys = fst bc (get ab-xs)

  ac : LensPart _ _
  get ac = get bc-ys
  set ac v = set ab-xs (set bc-ys v)

get-set (snd (ab ⋯ bc)) s v = cong (getter bc) (get-set (snd ab) s _) ; bc .snd .get-set (get (fst ab s)) v
set-get (snd (ab ⋯ bc)) s = cong (setter ab s) (set-get (snd bc) (get (fst ab s))) ; set-get (snd ab) s
set-set (snd (ab ⋯ bc)) s v₁ v₂ = set-set (snd ab) s _ _ ; cong (setter ab s) (cong (flip (setter bc) v₂) (get-set (snd ab) _ _) ; set-set (snd bc) _ _ _)
