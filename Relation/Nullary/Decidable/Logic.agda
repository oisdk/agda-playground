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

disj : (A → C) → (B → C) → (¬ A → ¬ B → ¬ C) → Dec A → Dec B → Dec C
disj l r n x y .does = x .does or y .does
disj l r n (yes x) y .why = l x
disj l r n (no  x) (yes y) .why = r y
disj l r n (no ¬x) (no ¬y) .why = n ¬x ¬y

conj : (A → B → C) → (¬ A → ¬ C) → (¬ B → ¬ C) → Dec A → Dec B → Dec C
conj c l r x y .does = x .does and y .does
conj c l r (no ¬x) y .why = l ¬x
conj c l r (yes x) (no ¬y) .why = r ¬y
conj c l r (yes x) (yes y) .why = c x y

! : Dec A → Dec (¬ A)
! x .does = not (x .does)
! (yes x) .why = (λ z → z x)
! (no  x) .why = x
