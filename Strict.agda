{-# OPTIONS --without-K --safe #-}

module Strict where

open import Agda.Builtin.Strict
open import Level

infixr 0 _$!_
_$!_ : {A : Type a} {B : A → Type b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f
{-# INLINE _$!_ #-}
