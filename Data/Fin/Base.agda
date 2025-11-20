{-# OPTIONS --without-K --safe #-}

module Data.Fin.Base where

open import Data.Maybe.Base
open import Data.Nat.Base using (ℕ; suc; zero)
open import Level
open import Data.Empty

Fin : ℕ → Type
Fin zero    = ⊥
Fin (suc n) = Maybe (Fin n)

pattern f0 = nothing
pattern fs n = just n

pattern f1 = fs f0
pattern f2 = fs f1
pattern f3 = fs f2
pattern f4 = fs f3
pattern f5 = fs f4
pattern f6 = fs f5
pattern f7 = fs f6
pattern f8 = fs f7
pattern f9 = fs f8
