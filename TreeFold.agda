{-# OPTIONS --cubical --safe #-}

module TreeFold where

open import Prelude
open import Data.List

record Node {a} (A : Type a) : Type a where
  constructor node
  field
    bit : Bool
    val : A
open Node

Spine : Type a → Type a
Spine A = List (Node A)

module _ {a} {A : Type a} (f : A → A → A) (z : A) where
  cons : A → Spine A → Spine A
  cons x [] = node false x ∷ []
  cons x (node false y ∷ xs) = node true (f x y) ∷ xs
  cons x (node true  y ∷ xs) = node false x ∷ cons y xs

  build : List A → Spine A
  build = foldr cons []

  run : Spine A → A
  run = foldr (f ∘ val) z

  treeFold : List A → A
  treeFold = run ∘ build
