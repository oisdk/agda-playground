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

sub₄ : (𝔹 → 𝔹) → (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹
sub₃ : (𝔹 → 𝔹) → (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹

sub₄ o k 0ᵇ         ys      = 0ᵇ
sub₄ o k (1ᵇ xs)    (1ᵇ ys) = sub₄ (λ x → o (k x)) 2ᵇ_ xs ys
sub₄ o k (2ᵇ xs)    (2ᵇ ys) = sub₄ (λ x → o (k x)) 2ᵇ_ xs ys
sub₄ o k (1ᵇ xs)    (2ᵇ ys) = sub₄ o (λ x → k (1ᵇ x)) xs ys
sub₄ o k (2ᵇ xs)    (1ᵇ ys) = sub₃ o (λ x → k (1ᵇ x)) xs ys
sub₄ o k (1ᵇ 0ᵇ)    0ᵇ      = o 0ᵇ
sub₄ o k (1ᵇ 1ᵇ xs) 0ᵇ      = o (k (1ᵇ (dec′ xs)))
sub₄ o k (1ᵇ 2ᵇ xs) 0ᵇ      = o (k (1ᵇ (1ᵇ xs)))
sub₄ o k (2ᵇ xs)    0ᵇ      = o (k (dec′ xs))

sub₃ o k 0ᵇ      0ᵇ      = o 0ᵇ
sub₃ o k 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₃ o k 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₃ o k (1ᵇ xs) 0ᵇ      = o (k (dec′ xs))
sub₃ o k (2ᵇ xs) 0ᵇ      = o (k (1ᵇ xs))
sub₃ o k (1ᵇ xs) (1ᵇ ys) = sub₃ o (λ x → k (1ᵇ x)) xs ys
sub₃ o k (2ᵇ xs) (2ᵇ ys) = sub₃ o (λ x → k (1ᵇ x)) xs ys
sub₃ o k (1ᵇ xs) (2ᵇ ys) = sub₄ (λ x → o (k x)) 2ᵇ_ xs ys
sub₃ o k (2ᵇ xs) (1ᵇ ys) = sub₃ (λ x → o (k x)) 2ᵇ_ xs ys

sub₂ : (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹
sub₂ k 0ᵇ      ys      = 0ᵇ
sub₂ k (1ᵇ xs) 0ᵇ      = k (dec′ xs)
sub₂ k (2ᵇ xs) 0ᵇ      = k (1ᵇ xs)
sub₂ k (1ᵇ xs) (1ᵇ ys) = sub₂ (λ x → 1ᵇ k x) xs ys
sub₂ k (2ᵇ xs) (2ᵇ ys) = sub₂ (λ x → 1ᵇ k x) xs ys
sub₂ k (1ᵇ xs) (2ᵇ ys) = sub₄ k 2ᵇ_ xs ys
sub₂ k (2ᵇ xs) (1ᵇ ys) = sub₃ k 2ᵇ_ xs ys

sub₁ : (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹
sub₁ k  xs     0ᵇ      = k xs
sub₁ k 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₁ k 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₁ k (1ᵇ xs) (1ᵇ ys) = sub₃ k 2ᵇ_ xs ys
sub₁ k (2ᵇ xs) (2ᵇ ys) = sub₃ k 2ᵇ_ xs ys
sub₁ k (2ᵇ xs) (1ᵇ ys) = sub₁ (λ x → 1ᵇ k x) xs ys
sub₁ k (1ᵇ xs) (2ᵇ ys) = sub₂ (λ x → 1ᵇ k x) xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
_-_ = sub₁ (λ x → x)
