{-# OPTIONS --cubical --safe #-}

module Testers where

open import Prelude
open import Data.List using (List; map; _⋯_)
open import Data.List.Sugar using (liftA2)

testIso : (fns : A ↔ B) → List A → Type _
testIso (to iff fro) xs = xs ≡ map (fro ∘ to) xs

testIsoℕ : (fns : ℕ ↔ A) → ℕ → Type _
testIsoℕ fns n = testIso fns (0 ⋯ n)

testUnary : (A → B) → (A → A) → (B → B) → List A → Type _
testUnary to f g xs =
  map (to ∘ f) xs ≡ map (g ∘ to) xs

testBinary : (A → B) → (A → A → A) → (B → B → B) → List A → Type _
testBinary to f g xs =
  liftA2 (λ x y → to (f x y)) xs xs ≡ liftA2 (λ x y → g (to x) (to y)) xs xs

testUnaryℕ : (ℕ → A) → (ℕ → ℕ) → (A → A) → ℕ → Type _
testUnaryℕ to f g n = testUnary to f g (0 ⋯ n)

testBinaryℕ : (ℕ → A) → (ℕ → ℕ → ℕ) → (A → A → A) → ℕ → Type _
testBinaryℕ to f g n = testBinary to f g (0 ⋯ n)
