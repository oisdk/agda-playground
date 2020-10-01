{-# OPTIONS --without-K --safe #-}

module Strict where

open import Agda.Builtin.Strict
open import Level

infixr 0 _$!_
_$!_ : {A : Type a} {B : A → Type b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f
{-# INLINE _$!_ #-}

infixr 0 bang
bang : {A : Type a} {B : A → Type b} → ∀ x → (∀ x → B x) → B x
bang = primForce
{-# INLINE bang #-}

syntax bang v (λ x → e) = let! x =! v in! e
