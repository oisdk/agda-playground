{-# OPTIONS --without-K --safe #-}

module Data.Binary.Conversion.Fast.Strict where

open import Data.Binary.Definition
open import Data.Nat.DivMod
open import Data.Nat.Base using (ℕ; suc; zero)
open import Strict
open import Data.Bool

⟦_⇑⟧⟨_⟩ : ℕ → ℕ → 𝔹
⟦ suc n ⇑⟧⟨ suc w ⟩ =
  let! m =! even n in!
  let! ms =! ⟦ n ÷ 2 ⇑⟧⟨ w ⟩ in!
  if m then 1ᵇ ms else 2ᵇ ms
⟦ zero  ⇑⟧⟨ _    ⟩ = 0ᵇ
⟦ suc _ ⇑⟧⟨ zero ⟩ = 0ᵇ -- will not happen

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

-- open import Data.Nat.WellFounded

-- ⟦_⇑⟧‴ : ℕ → 𝔹
-- ⟦ n ⇑⟧‴ = go n (≤-wellFounded n)
--   where
--   go : ∀ n → Acc _<_ n → 𝔹
--   go zero    wf = 0ᵇ
--   go (suc n) (acc wf) =
--     if rem n 2 ℕ.≡ᴮ 0
--     then 1ᵇ go (n ÷ 2) (wf (n ÷ 2) (s≤s (div2≤ n)))
--     else 2ᵇ go (n ÷ 2) (wf (n ÷ 2) (s≤s (div2≤ n)))
