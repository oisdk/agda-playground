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
  renaming
    ( congS to cong′
    ; _∙_ to _;_
    ; subst2 to subst₂)
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

cong₃ : ∀ {d} {D : Type d}
      → (f : A → B → C → D)
      → {x x′ : A}
      → {y y′ : B}
      → {z z′ : C}
      → x ≡ x′
      → y ≡ y′
      → z ≡ z′
      → f x y z ≡ f x′ y′ z′
cong₃ f x y z = cong₂ (λ f x → f x) (cong₂ f x y) z
