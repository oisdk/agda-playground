{-# OPTIONS --allow-unsolved-metas #-}

module Applicative where

open import Prelude
open import Algebra

module _ (mon : Monoid a) where
  open Monoid mon
  constApplicative : Applicative {ℓ₁ = b} (const 𝑆)
  constApplicative .Applicative.pure _ = ε
  constApplicative .Applicative._<*>_ = _∙_
  constApplicative .Applicative.pure-homo _ _ = ε∙ _
  constApplicative .Applicative.<*>-interchange u _ = ∙ε u ; sym (ε∙ _)
  constApplicative .Applicative.<*>-comp u v w = cong (λ eu → eu ∙ v ∙ w) (ε∙ u) ; assoc _ _ _

idApplicative : Applicative {ℓ₁ = a} id
idApplicative .Applicative.pure = id
idApplicative .Applicative._<*>_ = _$_
idApplicative .Applicative.pure-homo f x = refl
idApplicative .Applicative.<*>-interchange u y = refl
idApplicative .Applicative.<*>-comp u v w = refl


module _ {F : Type b → Type c} {G : Type a → Type b} (fa : Applicative F) (ga : Applicative G) where
  open Applicative ⦃ ... ⦄
  instance
    _ : Applicative F
    _ = fa

  instance
    _ : Applicative G
    _ = ga

  composeApplicative : Applicative (F ∘ G)
  composeApplicative .Applicative.pure x = pure (pure x)
  composeApplicative .Applicative._<*>_ fs xs = ⦇ fs <*> xs ⦈
  composeApplicative .Applicative.pure-homo f x = {!!}
  composeApplicative .Applicative.<*>-interchange u y = {!!}
  composeApplicative .Applicative.<*>-comp u v w = {!!}
