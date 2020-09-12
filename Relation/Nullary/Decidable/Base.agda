{-# OPTIONS --cubical --safe --postfix-projections #-}

module Relation.Nullary.Decidable.Base where

open import Level
open import Data.Bool
open import Data.Empty

data Reflects {a} (A : Type a) : Bool → Type a where
  ofʸ  : (p   :    A) → Reflects A true
  ofⁿ  : (¬p  : ¬  A) → Reflects A false

record Dec {a} (A : Type a) : Type a where
  constructor _because_
  field
    does  : Bool
    why   : Reflects A does
open Dec public

pattern yes p  = true   because ofʸ p
pattern no ¬p  = false  because ofⁿ ¬p

map-reflects : ∀ {d} → (A → B) → (¬ A → ¬ B) → Reflects A d → Reflects B d
map-reflects to fro (ofʸ p) = ofʸ (to p)
map-reflects to fro (ofⁿ ¬p) = ofⁿ (fro ¬p)

map-dec : (A → B) → (¬ A → ¬ B) → Dec A → Dec B
map-dec to fro dec .does = dec .does
map-dec to fro dec .why = map-reflects to fro (dec .why)

⟦yes_,no_⟧ : (A → B) → (B → A) → Dec A → Dec B
⟦yes to ,no fro ⟧ = map-dec to λ ¬A ¬B → ¬A (fro ¬B)

∣_∣yes⇒_∣no⇒_ : Dec A → (A → B) → (¬ A → ¬ B) → Dec B
∣ d ∣yes⇒ y ∣no⇒ n = map-dec y n d
