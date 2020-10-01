{-# OPTIONS --cubical --safe #-}

module Strict.Properties where

open import Path
open import Level
open import Strict
open import Agda.Builtin.Strict
open import Function

$!-≡ : {A : Type a} {B : A → Type b} → (f : ∀ x → B x) → ∀ x → (f $! x) ≡ f x
$!-≡ f x = builtin-eq-to-path (primForceLemma x f)

$!≡$ : {A : Type a} {B : A → Type b} → _$!_ {A = A} {B = B} ≡ _$_ {A = A} {B = B}
$!≡$ i f x = $!-≡ f x i
