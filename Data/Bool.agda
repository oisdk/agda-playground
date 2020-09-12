{-# OPTIONS --cubical --safe #-}

module Data.Bool where

open import Level
open import Agda.Builtin.Bool using (Bool; true; false) public
open import Data.Unit
open import Data.Empty

bool : ∀ {ℓ} {P : Bool → Type ℓ} (f : P false) (t : P true) → (x : Bool) → P x
bool f t false = f
bool f t true = t

not : Bool → Bool
not false = true
not true = false

infixl 6 _or_
_or_ : Bool → Bool → Bool
false or y = y
true  or y = true

infixl 7 _and_
_and_ : Bool → Bool → Bool
false and y = false
true  and y = y

infixr 0 if_then_else_
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then x else _ = x
if false then _ else x = x

T : Bool → Type₀
T true  = ⊤
T false = ⊥
