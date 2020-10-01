{-# OPTIONS --cubical --safe #-}

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

open import Path
open import Agda.Builtin.Equality hiding (_≡_)
import Agda.Builtin.Equality as MLTT

mltt-to-path : {A : Type a} {x y : A} → x MLTT.≡ y → x ≡ y
mltt-to-path {x = x} MLTT.refl i = x

$!-≡ : {A : Type a} {B : A → Type b} → (f : ∀ x → B x) → ∀ x → (f $! x) ≡ f x
$!-≡ f x = mltt-to-path (primForceLemma x f)

-- primForceLemma x f
-- $!-≡ f x | res = {!res!}
