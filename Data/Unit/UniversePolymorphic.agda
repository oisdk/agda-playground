{-# OPTIONS --safe --without-K #-}

module Data.Unit.UniversePolymorphic where

open import Level

record ⊤ {ℓ} : Type ℓ where constructor tt
