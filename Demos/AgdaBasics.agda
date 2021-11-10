{-# OPTIONS --cubical #-}

module Demos.AgdaBasics where

open import Level
open import Data.Nat
open import Data.String

data Bool : Type where
  false : Bool
  true  : Bool

and : Bool → Bool → Bool
and true true = true
and _    _    = false

-- _,not! : Bool → Bool
-- false ,not! = true
-- true  ,not! = false

-- _∧_ : Bool → Bool → Bool
-- false ∧ y = false
-- true  ∧ y = y

infixr 1 if_then_else_
if_then_else_ : Bool → A → A → A
if false then true-path else false-path = false-path
if true  then true-path else false-path = true-path

stringOrNat : (x : Bool) → if x then String else ℕ
stringOrNat true  = "it was a true!"
stringOrNat false = 42
