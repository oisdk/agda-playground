{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Decidable where

open import Level
open import Data.Bool
open import Data.Empty
open import Function.Biconditional

Reflects : Type a → Bool → Type a
Reflects A = bool′ (¬ A) A

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

Reflects-T : ∀ b → Reflects (T b) b
Reflects-T = bool (λ z → z) _

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

dec-bool : (b : Bool) → (T b → A) → (A → T b) → Dec A
dec-bool b to fro .does = b
dec-bool false to fro .why = fro
dec-bool true  to fro .why = to _

open import Path

it-does : (d : Dec A) → A → does d ≡ true
it-does (yes _) _ = refl
it-does (no ¬A) A = ⊥-elim (¬A A)

it-doesn't : (d : Dec A) → ¬ A → does d ≡ false
it-doesn't (no _)  _  = refl
it-doesn't (yes A) ¬A = ⊥-elim (¬A A)
