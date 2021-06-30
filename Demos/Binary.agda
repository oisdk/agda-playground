{-# OPTIONS --cubical --safe --postfix-projections #-}

module Demos.Binary where

open import Data.Nat
open import Testers
open import Prelude

infixl 5 _1𝕓 _2𝕓
data 𝔹 : Type where
  0𝕓  : 𝔹
  _1𝕓 : 𝔹 → 𝔹
  _2𝕓 : 𝔹 → 𝔹

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0𝕓 ⇓⟧ = 0
⟦ n 1𝕓 ⇓⟧ = 1 + ⟦ n ⇓⟧ * 2
⟦ n 2𝕓 ⇓⟧ = 2 + ⟦ n ⇓⟧ * 2

inc : 𝔹 → 𝔹
inc 0𝕓 = 0𝕓 1𝕓
inc (xs 1𝕓) = xs 2𝕓
inc (xs 2𝕓) = inc xs 1𝕓

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0𝕓
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-suc 0𝕓     i = 1
inc-suc (x 1𝕓) i = 2 + ⟦ x ⇓⟧ * 2
inc-suc (x 2𝕓) i = suc (inc-suc x i * 2)

inc-2*-1𝕓 : ∀ n → inc ⟦ n * 2 ⇑⟧ ≡ ⟦ n ⇑⟧ 1𝕓
inc-2*-1𝕓 zero    i = 0𝕓 1𝕓
inc-2*-1𝕓 (suc n) i = inc (inc (inc-2*-1𝕓 n i))

𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
𝔹-rightInv zero    = refl
𝔹-rightInv (suc x) = inc-suc ⟦ x ⇑⟧ ; cong suc (𝔹-rightInv x)

𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
𝔹-leftInv 0𝕓 = refl
𝔹-leftInv (x 1𝕓) =           inc-2*-1𝕓 ⟦ x ⇓⟧  ; cong _1𝕓 (𝔹-leftInv x)
𝔹-leftInv (x 2𝕓) = cong inc (inc-2*-1𝕓 ⟦ x ⇓⟧) ; cong _2𝕓 (𝔹-leftInv x)

ℕ⇔𝔹 : 𝔹 ⇔ ℕ
ℕ⇔𝔹 .fun = ⟦_⇓⟧
ℕ⇔𝔹 .inv = ⟦_⇑⟧
ℕ⇔𝔹 .rightInv = 𝔹-rightInv
ℕ⇔𝔹 .leftInv = 𝔹-leftInv
