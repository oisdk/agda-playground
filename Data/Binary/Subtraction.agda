{-# OPTIONS --without-K --safe #-}

module Data.Binary.Subtraction where

open import Data.Binary.Definition
open import Data.Nat

dec′ : 𝔹 → 𝔹
dec : 𝔹 → 𝔹

dec′ 0ᵇ = 0ᵇ
dec′ (1ᵇ xs) = 2ᵇ dec′ xs
dec′ (2ᵇ xs) = 2ᵇ 1ᵇ xs

dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = dec′ xs

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = ones n (1ᵇ xs)

push : 𝔹 → 𝔹 → 𝔹
push 0ᵇ     xs      = xs
push (2ᵇ t) xs      = push t (2ᵇ xs)
push (1ᵇ t) 0ᵇ      = push t 0ᵇ
push (1ᵇ t) (1ᵇ xs) = push t (1ᵇ xs)
push (1ᵇ t) (2ᵇ xs) = push t (2ᵇ 1ᵇ xs)

sub₄ : ℕ → 𝔹 → 𝔹 → 𝔹 → 𝔹
sub₃ : ℕ → 𝔹 → 𝔹 → 𝔹 → 𝔹

sub₄ n t 0ᵇ         ys      = 0ᵇ
sub₄ n t (1ᵇ xs)    (1ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₄ n t (1ᵇ xs)    (2ᵇ ys) = sub₄ n (1ᵇ t) xs ys
sub₄ n t (1ᵇ xs)    0ᵇ      = ones n (push (1ᵇ t) (dec′ xs))
sub₄ n t (2ᵇ xs)    (2ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₄ n t (2ᵇ xs)    (1ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₄ n t (2ᵇ xs)    0ᵇ      = ones n (push (2ᵇ t) (dec′ xs))

sub₃ n t 0ᵇ      0ᵇ      = ones n (push t 0ᵇ)
sub₃ n t 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₃ n t 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₃ n t (1ᵇ xs) 0ᵇ      = ones n (push t (2ᵇ dec′ xs))
sub₃ n t (2ᵇ xs) 0ᵇ      = ones n (push t (2ᵇ 1ᵇ xs))
sub₃ n t (1ᵇ xs) (1ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₃ n t (2ᵇ xs) (2ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₃ n t (1ᵇ xs) (2ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₃ n t (2ᵇ xs) (1ᵇ ys) = sub₃ n (2ᵇ t) xs ys

sub₂ : ℕ → 𝔹 → 𝔹 → 𝔹
sub₂ t 0ᵇ      ys      = 0ᵇ
sub₂ t (1ᵇ xs) 0ᵇ      = ones t (dec′ xs)
sub₂ t (2ᵇ xs) 0ᵇ      = ones t (1ᵇ xs)
sub₂ t (1ᵇ xs) (1ᵇ ys) = sub₂ (suc t) xs ys
sub₂ t (2ᵇ xs) (2ᵇ ys) = sub₂ (suc t) xs ys
sub₂ t (1ᵇ xs) (2ᵇ ys) = sub₄ t 0ᵇ xs ys
sub₂ t (2ᵇ xs) (1ᵇ ys) = sub₃ t 0ᵇ xs ys

sub₁ : ℕ → 𝔹 → 𝔹 → 𝔹
sub₁ t xs      0ᵇ      = ones t xs
sub₁ t 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₁ t 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₁ t (1ᵇ xs) (1ᵇ ys) = sub₃ t 0ᵇ xs ys
sub₁ t (2ᵇ xs) (2ᵇ ys) = sub₃ t 0ᵇ xs ys
sub₁ t (2ᵇ xs) (1ᵇ ys) = sub₁ (suc t) xs ys
sub₁ t (1ᵇ xs) (2ᵇ ys) = sub₂ (suc t) xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
_-_ = sub₁ zero
