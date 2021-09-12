{-# OPTIONS --safe #-}

module Data.Nat.AbsoluteDifference where

open import Data.Nat.Base
open import Path
open import Prelude
open import Algebra

∣_-_∣ : ℕ → ℕ → ℕ
∣ 0         - m     ∣ = m
∣ n@(suc _) - 0     ∣ = n
∣ suc n     - suc m ∣ = ∣ n - m ∣

_ : ∣ 5 - 3 ∣ ≡ 2
_ = refl

_ : ∣ 3 - 5 ∣ ≡ 2
_ = refl

∣-∣‿comm : Commutative ∣_-_∣
∣-∣‿comm zero    zero    = refl
∣-∣‿comm zero    (suc y) = refl
∣-∣‿comm (suc x) zero    = refl
∣-∣‿comm (suc x) (suc y) = ∣-∣‿comm x y
