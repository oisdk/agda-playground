{-# OPTIONS --cubical #-}

module Demos.AgdaBasics where

open import Level
open import Data.Nat
open import Data.String

data Bool : Type₀ where
  false : Bool
  true  : Bool

_,not! : Bool → Bool
false ,not! = true
true  ,not! = false

_∧_ : Bool → Bool → Bool
false ∧ y = false
true  ∧ y = y

infixr 1 if_then_else_
if_then_else_ : Bool → A → A → A
if false then true-path else false-path = false-path
if true  then true-path else false-path = true-path

natOrString : (x : Bool) → if x then ℕ else String
natOrString true  = 4
natOrString false = "false"
