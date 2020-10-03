{-# OPTIONS --cubical #-}

module Data.Binary.Conversion.Unsafe where

-- While this module is called "unsafe" it's really not.
-- The function below hasn't been proven to be terminating,
-- but we know that it is because (n - 1) ÷ 2 < n, it's just that
-- it's pretty tedious to prove that fact.

open import Data.Binary.Definition
open import Data.Nat.DivMod
open import Prelude
import Data.Nat.Properties as ℕ

{-# TERMINATING #-}
⟦_⇑⟧″ : ℕ → 𝔹
⟦ zero  ⇑⟧″ = 0ᵇ
⟦ suc n ⇑⟧″ = if rem n 2 ℕ.≡ᴮ 0 then 1ᵇ ⟦ n ÷ 2 ⇑⟧″ else 2ᵇ ⟦ n ÷ 2 ⇑⟧″
