{-# OPTIONS --without-K --safe #-}

module Data.Fin.Indexed.Properties where

open import Agda.Builtin.Nat using (_<_)
open import Data.Nat.Base
open import Data.Fin.Indexed.Base
open import Data.Bool
open import Data.Maybe.Base

private variable n m k : ℕ

weaken : ∀ {n} → Fin n → Fin (suc n)
weaken {suc n} f0 = f0
weaken {suc n} (fs x) = fs (weaken x)

-- x \\ y | x < y = just x
--        | x ≡ y = nothing
--        | x > y = just (x - 1)
_\\_ : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
f0   \\ f0   = nothing
fs i \\ f0   = just i
_\\_ {suc n} (fs i) (fs j) = mapMaybe fs (i \\ j)
_\\_ {suc n} (f0  ) (fs j) = just f0

insert : Fin (suc n) → Fin n → Fin (suc n)
insert f0     j      = fs j
insert (fs i) f0     = f0
insert (fs i) (fs j) = fs (insert i j)

weakens : ∀ n → Fin m → Fin (n + m)
weakens zero    x = x
weakens (suc n) x = weaken (weakens n x)

_∔_ : Fin n → Fin m → Fin (n + m)
f0   ∔ m = weakens _ m
fs n ∔ m = fs (n ∔ m)

under : (Fin m → Fin k) → Fin (n + m) → Fin (n + k)
under {n = zero } f x      = f x
under {n = suc n} f (fs x) = fs (under f x)
under {n = suc n} f f0     = f0
