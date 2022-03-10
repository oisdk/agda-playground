{-# OPTIONS --without-K --safe #-}

module Data.Binary.Conversion.Fast where

-- This module provides a conversion function from
-- nats which uses built-in functions.
-- It is dramatically faster than the normal conversion
-- even at smaller numbers.

open import Data.Binary.Definition
open import Data.Nat.DivMod
open import Data.Nat.Base
open import Data.Bool

⟦_⇑⟧⟨_⟩ : ℕ → ℕ → 𝔹
⟦ suc n ⇑⟧⟨ suc w ⟩ =
  if even n
    then 1ᵇ ⟦ n ÷ 2 ⇑⟧⟨ w ⟩
    else 2ᵇ ⟦ n ÷ 2 ⇑⟧⟨ w ⟩
⟦ zero  ⇑⟧⟨ _    ⟩ = 0ᵇ
⟦ suc _ ⇑⟧⟨ zero ⟩ = 0ᵇ -- will not happen

-- We build the output by repeatedly halving the input,
-- but we also pass in the number to reduce as we go so that
-- we satisfy the termination checker.
⟦_⇑⟧ : ℕ → 𝔹
⟦ n ⇑⟧ = ⟦ n ⇑⟧⟨ n ⟩
{-# INLINE ⟦_⇑⟧ #-}

-- Without the added argument to the recursor, the function does not
-- pass the termination checker:
-- {-# TERMINATING #-}
-- ⟦_⇑⟧″ : ℕ → 𝔹
-- ⟦ zero  ⇑⟧″ = 0ᵇ
-- ⟦ suc n ⇑⟧″ =
--   if rem n 2 ℕ.≡ᴮ 0
--   then 1ᵇ ⟦ n ÷ 2 ⇑⟧″
--   else 2ᵇ ⟦ n ÷ 2 ⇑⟧″

-- The "principled" version (which uses well-founded recursion) is
-- incredibly slow. (and the following doesn't even compute, because of
-- cubical)

open import Data.Nat.WellFounded
open import WellFounded

⟦_⇑⟧‴ : ℕ → 𝔹
⟦ n ⇑⟧‴ = go n (≤-wellFounded n)
  where
  go : ∀ n → Acc _<_ n → 𝔹
  go zero    wf = 0ᵇ
  go (suc n) (acc wf) =
    if even n
    then 1ᵇ go (n ÷ 2) (wf (n ÷ 2) (s≤s (div2≤ n)))
    else 2ᵇ go (n ÷ 2) (wf (n ÷ 2) (s≤s (div2≤ n)))

-- open import Path

-- _ : ⟦ 3 ⇑⟧‴ ≡ 1ᵇ 1ᵇ 0ᵇ
-- _ = refl
