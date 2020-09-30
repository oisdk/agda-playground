{-# OPTIONS --cubical --safe #-}

module Data.Binary.PerformanceTests.Subtraction where

open import Prelude
open import Data.Binary.Definition
open import Data.Binary.Addition using (_+_)
open import Data.Binary.Subtraction using (_-_)
open import Data.Binary.Multiplication using (_*_)

sub-r  : 𝔹 → 𝔹 → ℕ → 𝔹
sub-r a x zero = a
sub-r a x (suc n) = sub-r a x n - x

sub-l  : 𝔹 → 𝔹 → ℕ → 𝔹
sub-l a x zero = a
sub-l a x (suc n) = sub-r (a - x) x n

one-thousand : 𝔹
one-thousand = 2ᵇ 1ᵇ 1ᵇ 2ᵇ 1ᵇ 2ᵇ 2ᵇ 2ᵇ 2ᵇ 0ᵇ

f : 𝔹
f = one-thousand * one-thousand * one-thousand

n : ℕ
n = 99999

-- The actual performance test (uncomment and time how long it takes to type-check)
-- _ : sub-l f one-thousand n ≡ sub-r f one-thousand n
-- _ = refl
