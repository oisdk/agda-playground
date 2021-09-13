{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Algebra

module Data.Maybe.Monoid {ℓ} (sgr : Semigroup ℓ) where

open import Data.Maybe

open Semigroup sgr

_«∙»_ : Maybe 𝑆 → Maybe 𝑆 → Maybe 𝑆
nothing «∙» y = y
just x «∙» nothing = just x
just x «∙» just y = just (x ∙ y)

maybeMonoid : Monoid ℓ
maybeMonoid .Monoid.𝑆 = Maybe 𝑆
maybeMonoid .Monoid._∙_ = _«∙»_
maybeMonoid .Monoid.ε = nothing
maybeMonoid .Monoid.assoc nothing y z = refl
maybeMonoid .Monoid.assoc (just x) nothing z = refl
maybeMonoid .Monoid.assoc (just x) (just x₁) nothing = refl
maybeMonoid .Monoid.assoc (just x) (just y) (just z) = cong just (assoc x y z)
maybeMonoid .Monoid.ε∙ _ = refl
maybeMonoid .Monoid.∙ε nothing = refl
maybeMonoid .Monoid.∙ε (just x) = refl
