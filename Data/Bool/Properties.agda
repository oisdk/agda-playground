{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Bool.Properties where

open import HLevels
open import Path
open import Data.Bool.Base
open import Data.Bool.Truth
open import Data.Unit.Properties
open import Data.Unit
open import Data.Empty
open import Data.Empty.Properties using (isProp⊥)
open import Relation.Nullary.Discrete
open import Relation.Nullary.Discrete.Properties
open import Relation.Nullary.Decidable using (Dec; does; why)

isPropT : ∀ x → isProp (T x)
isPropT false = isProp⊥
isPropT true  = isProp⊤

false≢true : false ≢ true
false≢true p = subst (bool ⊤ ⊥) p tt

true≢false : true ≢ false
true≢false p = subst (bool ⊥ ⊤) p tt

discreteBool : Discrete Bool
discreteBool false y .does = not y
discreteBool true y .does = y
discreteBool false false .why = refl
discreteBool false true .why = false≢true
discreteBool true false .why = true≢false
discreteBool true true .why = refl

isSetBool : isSet Bool
isSetBool = Discrete→isSet discreteBool
