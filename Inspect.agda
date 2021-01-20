{-# OPTIONS --cubical --safe #-}

module Inspect where

open import Level
open import Path

record Reveal_·_is_ {A : Type a} {B : A → Type b} (f : (x : A) → B x) (x : A) (y : B x) : Type b where
  constructor 〖_〗
  field eq : f x ≡ y

inspect : {A : Type a} {B : A → Type b} (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = 〖 refl 〗
