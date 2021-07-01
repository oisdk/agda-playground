{-# OPTIONS --safe --cubical #-}

module Lens.Operators where

open import Prelude
open import Lens.Definition

infixl 4 getter setter

getter : Lens A B → A → B
getter l xs = get (fst l xs)

syntax getter l xs = xs [ l ]

setter : Lens A B → A → B → A
setter l xs = set (fst l xs)

syntax setter l xs x = xs [ l ]≔ x
