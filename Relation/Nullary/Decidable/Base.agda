{-# OPTIONS --cubical --safe --postfix-projections #-}

module Relation.Nullary.Decidable.Base where

open import Level
open import Data.Bool
open import Data.Empty
open import Function.Biconditional

Reflects : Type a → Bool → Type a
Reflects A true  = A
Reflects A false = ¬ A

record Dec {a} (A : Type a) : Type a where
  constructor _because_
  field
    does  : Bool
    why   : Reflects A does
open Dec public

pattern yes p  = true   because p
pattern no ¬p  = false  because ¬p

map-reflects : (A → B) → (¬ A → ¬ B) → ∀ {d} → Reflects A d → Reflects B d
map-reflects {A = A} {B = B} to fro {d = d} = bool {P = λ d → Reflects A d → Reflects B d} fro to d

map-dec : (A → B) → (¬ A → ¬ B) → Dec A → Dec B
map-dec to fro dec .does = dec .does
map-dec to fro dec .why = map-reflects to fro (dec .why)

iff-dec : (A ↔ B) → Dec A → Dec B
iff-dec (to iff fro) = map-dec to (λ ¬y x → ¬y (fro x))

infixr 1 dec
dec : (A → B) → (¬ A → B) → Dec A → B
dec {A = A} {B = B} on-yes on-no d = bool {P = λ d → Reflects A d → B} on-no on-yes (d .does) (d .why)

syntax dec (λ yv → ye) (λ nv → ne) dc = ∣ dc ∣yes yv ⇒ ye ∣no nv ⇒ ne

T? : (b : Bool) → Dec (T b)
T? b .does = b
T? false .why ()
T? true  .why = _
