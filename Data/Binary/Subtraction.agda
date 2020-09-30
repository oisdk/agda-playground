{-# OPTIONS --without-K --safe #-}

module Data.Binary.Subtraction where

open import Data.Binary.Definition

dec′ : 𝔹 → 𝔹
dec : 𝔹 → 𝔹

dec′ 0ᵇ = 0ᵇ
dec′ (1ᵇ xs) = 2ᵇ dec′ xs
dec′ (2ᵇ xs) = 2ᵇ 1ᵇ xs

dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = dec′ xs

unsign : 𝔹 → 𝔹
unsign 0ᵇ = 0ᵇ
unsign (1ᵇ xs) = xs
unsign (2ᵇ xs) = 2ᵇ xs

shft₁ : 𝔹 → 𝔹
shft₁ 0ᵇ = 0ᵇ
shft₁ (1ᵇ xs) = 1ᵇ xs
shft₁ (2ᵇ xs) = 2ᵇ 1ᵇ xs

shft₂ : 𝔹 → 𝔹
shft₂ 0ᵇ = 0ᵇ
shft₂ (1ᵇ xs) = 2ᵇ xs
shft₂ (2ᵇ xs) = 2ᵇ 2ᵇ xs

shft₃ : 𝔹 → 𝔹
shft₃ 0ᵇ = 0ᵇ
shft₃ (1ᵇ xs) = 1ᵇ 1ᵇ xs
shft₃ (2ᵇ xs) = 1ᵇ 1ᵇ 2ᵇ xs

sub₄ : 𝔹 → 𝔹 → 𝔹
sub₃ : 𝔹 → 𝔹 → 𝔹

sub₄ 0ᵇ         ys      = 0ᵇ
sub₄ (1ᵇ xs)    (1ᵇ ys) = shft₂ (sub₄ xs ys)
sub₄ (2ᵇ xs)    (2ᵇ ys) = shft₂ (sub₄ xs ys)
sub₄ (1ᵇ xs)    (2ᵇ ys) = shft₁ (sub₄ xs ys)
sub₄ (2ᵇ xs)    (1ᵇ ys) = shft₁ (sub₃ xs ys)
sub₄ (1ᵇ 0ᵇ)    0ᵇ      = 1ᵇ 0ᵇ
sub₄ (1ᵇ 1ᵇ xs) 0ᵇ      = 2ᵇ 1ᵇ dec′ xs
sub₄ (1ᵇ 2ᵇ xs) 0ᵇ      = 2ᵇ 1ᵇ 1ᵇ xs
sub₄ (2ᵇ xs)    0ᵇ      = 2ᵇ dec′ xs

sub₃ 0ᵇ      0ᵇ      = 1ᵇ 0ᵇ
sub₃ 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₃ 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₃ (1ᵇ xs) 0ᵇ      = 2ᵇ dec′ xs
sub₃ (2ᵇ xs) 0ᵇ      = 2ᵇ 1ᵇ xs
sub₃ (1ᵇ xs) (1ᵇ ys) = shft₁ (sub₃ xs ys)
sub₃ (2ᵇ xs) (2ᵇ ys) = shft₁ (sub₃ xs ys)
sub₃ (1ᵇ xs) (2ᵇ ys) = shft₂ (sub₄ xs ys)
sub₃ (2ᵇ xs) (1ᵇ ys) = shft₂ (sub₃ xs ys)

sub₂ : 𝔹 → 𝔹 → 𝔹
sub₂ 0ᵇ      ys      = 0ᵇ
sub₂ (1ᵇ xs) 0ᵇ      = 1ᵇ dec′ xs
sub₂ (2ᵇ xs) 0ᵇ      = 1ᵇ 1ᵇ xs
sub₂ (1ᵇ xs) (1ᵇ ys) = shft₃ (sub₂ xs ys)
sub₂ (2ᵇ xs) (2ᵇ ys) = shft₃ (sub₂ xs ys)
sub₂ (1ᵇ xs) (2ᵇ ys) = sub₄ xs ys
sub₂ (2ᵇ xs) (1ᵇ ys) = sub₃ xs ys

sub₁ : 𝔹 → 𝔹 → 𝔹
sub₁ xs      0ᵇ      = 1ᵇ xs
sub₁ 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₁ 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₁ (1ᵇ xs) (1ᵇ ys) = sub₃ xs ys
sub₁ (2ᵇ xs) (2ᵇ ys) = sub₃ xs ys
sub₁ (2ᵇ xs) (1ᵇ ys) = shft₃ (sub₁ xs ys)
sub₁ (1ᵇ xs) (2ᵇ ys) = shft₃ (sub₂ xs ys)

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
xs - ys = unsign (sub₁ xs ys)
