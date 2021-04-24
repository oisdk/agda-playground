{-# OPTIONS --cubical --safe --postfix-projections #-}

module Relation.Nullary.Decidable.Logic where

open import Prelude
open import Data.Sum
open import Relation.Nullary.Decidable

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

negate : (A → ¬ B) → (¬ A → B) → Dec A → Dec B
negate t f d .does = not (d .does)
negate t f (yes d) .why = t d
negate t f (no ¬d) .why = f ¬d

! : Dec A → Dec (¬ A)
! = negate (λ x ¬x → ¬x x) id

infixl 7 _&&_
_&&_ : Dec A → Dec B → Dec (A × B)
_&&_ = conj _,_ (_∘ fst) (_∘ snd)

infixl 6 _||_
_||_ : Dec A → Dec B → Dec (A ⊎ B)
_||_ = disj inl inr either
