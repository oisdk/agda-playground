{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Bool.Properties where

open import Prelude
open import Data.Bool
open import Data.Unit.Properties

T? : ∀ x → Dec (T x)
T? x .does = x
T? false .why = ofⁿ id
T? true  .why = ofʸ tt

isPropT : ∀ x → isProp (T x)
isPropT false = isProp⊥
isPropT true  = isProp⊤

discreteBool : Discrete Bool
discreteBool false y .does = not y
discreteBool true y .does = y
discreteBool false false .why = ofʸ refl
discreteBool false true .why = ofⁿ λ p → subst (bool ⊤ ⊥) p tt
discreteBool true false .why = ofⁿ λ p → subst (bool ⊥ ⊤) p tt
discreteBool true true .why = ofʸ refl
