{-# OPTIONS --cubical --safe #-}

module Data.String where

open import Agda.Builtin.String using (String) public
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Agda.Builtin.Char using (Char) public
open import Agda.Builtin.Char
open import Agda.Builtin.Char.Properties
open import Relation.Binary
open import Relation.Binary.Construct.On
import Data.Nat.Order as ℕ
open import Function.Injective
open import Function
open import Path
open import Data.List
open import Data.List.Relation.Binary.Lexicographic

unpack : String → List Char
unpack = primStringToList

pack : List Char → String
pack = primStringFromList

charOrd : TotalOrder Char _ _
charOrd = on-ord primCharToNat lemma ℕ.totalOrder
  where
  lemma : Injective primCharToNat
  lemma x y p = builtin-eq-to-path (primCharToNatInjective x y (path-to-builtin-eq p ))

listCharOrd : TotalOrder (List Char) _ _
listCharOrd = listOrd charOrd

stringOrd : TotalOrder String _ _
stringOrd = on-ord primStringToList lemma listCharOrd
  where
  lemma : Injective primStringToList
  lemma x y p = builtin-eq-to-path (primStringToListInjective x y (path-to-builtin-eq p))
