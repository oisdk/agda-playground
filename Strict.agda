{-# OPTIONS --without-K --safe #-}

module Strict where

open import Agda.Builtin.Strict public
open import Level

infixr 0 _$!_
_$!_ : {A : Type a} {B : A → Type b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

infixr 0 let-bang
let-bang : {A : Type a} {B : A → Type b} → ∀ x → (∀ x → B x) → B x
let-bang = primForce
{-# INLINE let-bang #-}

syntax let-bang v (λ x → e) = let! x =! v in! e

infixr 0 lambda-bang
lambda-bang : {A : Type a} {B : A → Type b} → (∀ x → B x) → ∀ x → B x
lambda-bang f x = primForce x f
{-# INLINE lambda-bang #-}

syntax lambda-bang (λ x → e) = λ! x →! e
