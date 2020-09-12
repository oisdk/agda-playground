{-# OPTIONS --safe --cubical #-}

module Lens.Operators where

open import Prelude
open import Lens.Definition

infixl 4 _[_] _[_]≔_
_[_] : A → Lens A B → B
xs [ l ] = l .into xs .get

_[_]≔_ : A → Lens A B → B → A
xs [ l ]≔ x = l .into xs .set x
