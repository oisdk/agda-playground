{-# OPTIONS --cubical --safe #-}

module Path where

open import Cubical.Foundations.Everything
  using ( _≡_
        ; sym
        ; refl
        ; subst
        ; transport
        ; Path
        ; PathP
        ; I
        ; i0
        ; i1
        ; funExt
        ; cong
        ; toPathP
        ; cong₂
        ; ~_
        ; _∧_
        ; _∨_
        ; hcomp
        ; transp
        ; J
        )
  renaming (_∙_ to _;_)
  public

open import Data.Empty using (¬_)
open import Level

infix 4 _≢_
_≢_ : {A : Type a} → A → A → Type a
x ≢ y = ¬ (x ≡ y)

infix 4 PathP-syntax
PathP-syntax = PathP
{-# DISPLAY PathP-syntax = PathP #-}

syntax PathP-syntax (λ i → Ty) lhs rhs = lhs ≡[ i ≔ Ty ]≡ rhs

import Agda.Builtin.Equality as MLTT

builtin-eq-to-path : {A : Type a} {x y : A} → x MLTT.≡ y → x ≡ y
builtin-eq-to-path {x = x} MLTT.refl i = x

path-to-builtin-eq : {A : Type a} {x y : A} → x ≡ y → x MLTT.≡ y
path-to-builtin-eq {x = x} x≡y = subst (x MLTT.≡_) x≡y MLTT.refl
