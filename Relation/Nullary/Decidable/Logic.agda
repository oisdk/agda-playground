{-# OPTIONS --cubical --safe --postfix-projections #-}

module Relation.Nullary.Decidable.Logic where

open import Prelude
open import Data.Sum

infixl 7 _&&_
_&&_ : Dec A → Dec B → Dec (A × B)
(x && y) .does = x .does and y .does
(yes x && yes y) .why  = (x , y)
(yes x && no  y) .why  = (y ∘ snd)
(no  x && y) .why  = (x ∘ fst)

infixl 6 _||_
_||_ : Dec A → Dec B → Dec (A ⊎ B)
(x || y) .does = x .does or y .does
(yes x || y) .why = (inl x)
(no  x || yes y) .why = (inr y)
(no  x || no  y) .why = (either x y)

! : Dec A → Dec (¬ A)
! x .does = not (x .does)
! (yes x) .why = (λ z → z x)
! (no  x) .why = x
