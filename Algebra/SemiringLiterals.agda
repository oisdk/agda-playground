{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Level

module Algebra.SemiringLiterals {r} {𝑅 : Type r} (rng : Semiring 𝑅) where

open Semiring rng

open import Literals.Number
open import Data.Nat.Literals
open import Data.Unit
import Data.Unit.UniversePolymorphic as Poly
open import Data.Nat.DivMod
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Data.Bool
open import Strict

2# : 𝑅
2# = 1# + 1#

sringFromNatRec : ℕ → ℕ → 𝑅
sringFromNatRec zero    _       = 0#
sringFromNatRec (suc 0) _       = 1#
sringFromNatRec (suc 1) _       = 2#
sringFromNatRec (suc 2) _       = 1# + 2#
sringFromNatRec (suc n) (suc w) =
  let! r =! sringFromNatRec (n ÷ 2) w in!
  if even n
    then 1# + (r * 2#)
    else (1# + r) * 2#
sringFromNatRec _ zero = 0# -- will not happen

sringFromNat : ℕ → 𝑅
sringFromNat n = sringFromNatRec n n

instance
  numberRng : Number 𝑅
  Number.Constraint numberRng _ = Poly.⊤
  Number.fromNat numberRng n = sringFromNat n
