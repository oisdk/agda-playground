{-# OPTIONS --cubical #-}

module Data.Binary.Conversion.Unsafe where

-- While this module is called "unsafe" it's really not.
-- The function below has been proven to be terminating,
-- but the proof incurs a performance penalty.


open import Data.Binary.Definition
open import Data.Nat.DivMod
open import Prelude
import Data.Nat.Properties as ℕ

{-# TERMINATING #-}
⟦_⇑⟧″ : ℕ → 𝔹
⟦ zero  ⇑⟧″ = 0ᵇ
⟦ suc n ⇑⟧″ =
  if rem n 2 ℕ.≡ᴮ 0
  then 1ᵇ ⟦ n ÷ 2 ⇑⟧″
  else 2ᵇ ⟦ n ÷ 2 ⇑⟧″

open import Data.Nat.WellFounded

⟦_⇑⟧‴ : ℕ → 𝔹
⟦ n ⇑⟧‴ = go n (≤-wellFounded n)
  where
  go : ∀ n → Acc _<_ n → 𝔹
  go zero    wf = 0ᵇ
  go (suc n) (acc wf) =
    if rem n 2 ℕ.≡ᴮ 0
    then 1ᵇ go (n ÷ 2) (wf (n ÷ 2) (s≤s (div2≤ n)))
    else 2ᵇ go (n ÷ 2) (wf (n ÷ 2) (s≤s (div2≤ n)))
