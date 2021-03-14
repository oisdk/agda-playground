{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.SemiringLiterals {r} (rng : Semiring r) where

open Semiring rng

open import Literals.Number
open import Data.Nat.Literals
open import Data.Unit
import Data.Unit.UniversePolymorphic as Poly
open import Data.Nat.DivMod
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Data.Bool

2# : 𝑅
2# = 1# + 1#

⟦_⇑⟧⟨_⟩ : ℕ → ℕ → 𝑅
⟦ suc n ⇑⟧⟨ suc w ⟩ =
  if even n
    then 1# + ⟦ n ÷ 2 ⇑⟧⟨ w ⟩ * 2#
    else 2# + ⟦ n ÷ 2 ⇑⟧⟨ w ⟩ * 2#
⟦ zero  ⇑⟧⟨ _    ⟩ = 0#
⟦ suc _ ⇑⟧⟨ zero ⟩ = 0# -- will not happen

⟦_⇑⟧ : ℕ → 𝑅
⟦ n ⇑⟧ = ⟦ n ⇑⟧⟨ n ⟩

instance
  numberRng : Number 𝑅
  Number.Constraint numberRng _ = Poly.⊤
  Number.fromNat numberRng n = ⟦ n ⇑⟧
