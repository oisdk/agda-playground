{-# OPTIONS --cubical --safe #-}

module Data.Tree.Rose where

open import Prelude
open import Data.List

infixr 5 _&_
record Tree {a} (A : Type a) : Type a where
  inductive
  constructor _&_
  field
    root : A
    children : List (Tree A)
open Tree public
