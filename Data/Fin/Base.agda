{-# OPTIONS --cubical --safe #-}

module Data.Fin.Base where

open import Data.Maybe.Base
open import Data.Nat.Base using (ℕ; suc; zero)
open import Level
open import Data.Empty

Fin : ℕ → Type₀
Fin zero    = ⊥
Fin (suc n) = Maybe (Fin n)

pattern f0 = nothing
pattern fs n = just n
