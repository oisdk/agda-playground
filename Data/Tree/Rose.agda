{-# OPTIONS --cubical --safe #-}

module Data.Tree.Rose where

open import Prelude
open import Data.List


mutual
  Forest : Type a → Type a
  Forest A = List (Tree A)

  infixr 5 _&_
  record Tree {a} (A : Type a) : Type a where
    inductive
    constructor _&_
    field
      root : A
      children : Forest A
open Tree public


module WikiTree where
  open import Data.List.Syntax
  wikiTree : Tree ℕ
  wikiTree =
      1 &
        [ 2 &
            [ 5 &
                [ 9  & []
                , 10 & [] ]
            , 6 & [] ]
        , 3 & []
        , 4 &
            [ 7 &
                [ 11 & []
                , 12 & [] ]
            , 8 & [] ] ]
