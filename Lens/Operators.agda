{-# OPTIONS --safe --cubical #-}

module Lens.Operators where

open import Prelude
open import Lens.Definition

infixl 4 getter setter

getter : Lens A B → A → B
getter l xs = get (into l xs)

syntax getter xs l = xs [ l ]

setter : Lens A B → A → B → A
setter l xs = set (into l xs)

syntax setter l xs x = xs [ l ]≔ x
