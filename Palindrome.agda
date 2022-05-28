module Palindrome where

open import Prelude
open import Data.Vec
open import Data.Nat.Properties

private variable n m : ℕ

-- module _ (_≟_ : Discrete A) where
--   go : Vec A n → Vec A m → m ≤ n → ∃ k × Vec A k × Bool
--   go (_ ∷ ys) (_ ∷ [])     _ = _ , ys , true
--   go ys       []           _ = _ , ys , true
--   go (y ∷ ys) (_ ∷ _ ∷ zs) p = f y (go ys zs {!!})
--     where
--     f : A → ∃ k × Vec A k × Bool → ∃ k × Vec A k × Bool
--     f x (_ , y ∷ ys , r) = (_ , ys , does (x ≟ y) and r)

  -- isPal : Vec A n → Bool
  -- isPal xs = go xs xs .snd

