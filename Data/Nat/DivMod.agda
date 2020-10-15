{-# OPTIONS --cubical --safe #-}

module Data.Nat.DivMod where

open import Data.Nat.Base
open import Agda.Builtin.Nat as Nat
open import Data.Bool

nonZero : ℕ → Bool
nonZero (suc _) = true
nonZero zero    = false


infixl 8 _÷_
_÷_ : (n m : ℕ) → { m≢0 : T (nonZero m) } → ℕ
_÷_ n (suc m) = Nat.div-helper 0 m n m

rem : (n m : ℕ) → { m≢0 : T (nonZero m) } → ℕ
rem n (suc m) = Nat.mod-helper 0 m n m
