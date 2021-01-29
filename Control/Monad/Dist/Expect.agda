{-# OPTIONS --cubical --safe #-}

open import Algebra
open import HLevels

module Control.Monad.Dist.Expect {ℓ} (rng : Semiring ℓ) (cIsSet : isSet (Semiring.𝑅 rng)) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import Control.Monad.Dist.Definition rng
open import Control.Monad.Dist.Eliminators rng

expect-alg : (A → 𝑅) → W-ϕ[ A ] 𝑅
[ expect-alg f ]-set = cIsSet
[ expect-alg f ] p & x ∷ xs ⟨ Pxs ⟩ = p * f x + Pxs
[ expect-alg f ][] = 0#
[ expect-alg f ]-dup p q x _ xs =
  p * f x + (q * f x + xs) ≡˘⟨ +-assoc (p * f x) (q * f x) xs ⟩
  (p * f x + q * f x) + xs ≡˘⟨ cong (_+ xs) (⟨+⟩* p q (f x)) ⟩
  (p + q) * f x + xs ∎
[ expect-alg f ]-com p x q y _ xs =
  p * f x + (q * f y + xs) ≡˘⟨ +-assoc (p * f x) (q * f y) (xs) ⟩
  p * f x + q * f y + xs   ≡⟨ cong (_+ xs) (+-comm (p * f x) (q * f y)) ⟩
  q * f y + p * f x + xs   ≡⟨ +-assoc (q * f y) (p * f x) (xs) ⟩
  q * f y + (p * f x + xs) ∎
[ expect-alg f ]-del x _ xs =
  0# * f x + xs ≡⟨ cong (_+ xs) (0* (f x)) ⟩
  0# + xs       ≡⟨ 0+ xs ⟩
  xs            ∎

∫ : (A → 𝑅) → W A → 𝑅
∫ f xs = expect-alg f ↓ xs

syntax ∫ (λ x → e) = ∫ e 𝑑 x
