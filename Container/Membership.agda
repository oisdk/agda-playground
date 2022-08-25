{-# OPTIONS --safe --cubical #-}

open import Container

module Container.Membership (𝒞 : Container) where

open import Prelude
open import HLevels

infixr 5 _∈_ _∈!_
_∈_ : A → ⟦ 𝒞 ⟧ A → Type _
x ∈ xs = fiber (snd xs) x

_∈!_ : A → ⟦ 𝒞 ⟧ A → Type _
x ∈! xs = isContr (x ∈ xs)
