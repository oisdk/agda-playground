{-# OPTIONS --cubical --safe #-}

module Data.Nat.Base where

open import Agda.Builtin.Nat public
  using (_+_; _*_; zero; suc)
  renaming (Nat to ℕ; _-_ to _∸_)
import Agda.Builtin.Nat as Nat

open import Level
open import Data.Bool

data Ordering : ℕ → ℕ → Type₀ where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
... | less    m k = less (suc m) k
... | equal   m   = equal (suc m)
... | greater n k = greater (suc n) k

nonZero : ℕ → Bool
nonZero (suc _) = true
nonZero zero    = false

_÷_ : (n m : ℕ) → { m≢0 : T (nonZero m) } → ℕ
_÷_ n (suc m) = Nat.div-helper 0 m n m

rem : (n m : ℕ) → { m≢0 : T (nonZero m) } → ℕ
rem n (suc m) = Nat.mod-helper 0 m n m
