{-# OPTIONS --safe #-}

module Data.Vec.Sigma where

open import Prelude
open import Data.Unit.UniversePolymorphic renaming (⊤ to ⊤′)

Vec⁺ : Type a → ℕ → Type a
Vec⁺ A zero    = A
Vec⁺ A (suc n) = A × Vec⁺ A n

Vec : Type a → ℕ → Type a
Vec A 0       = ⊤′
Vec A (suc n) = Vec⁺ A n

private variable n : ℕ

open import Data.List using (List; _∷_; [])

toList⁺ : Vec⁺ A n → List A
toList⁺ {n = zero } x = x ∷ []
toList⁺ {n = suc n} (x , xs) = x ∷ toList⁺ xs

toList : Vec A n → List A
toList {n = zero } _ = []
toList {n = suc n} = toList⁺
