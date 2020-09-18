{-# OPTIONS --without-K --safe #-}

module Data.Binary.Subtraction where

open import Data.Binary.Definition

dec′ : 𝔹 → 𝔹
dec : 𝔹 → 𝔹

dec′ [] = []
dec′ (1ᵇ∷ xs) = 2ᵇ∷ dec′ xs
dec′ (2ᵇ∷ xs) = 2ᵇ∷ 1ᵇ∷ xs

dec [] = []
dec (2ᵇ∷ xs) = 1ᵇ∷ xs
dec (1ᵇ∷ xs) = dec′ xs

sub₄ : (𝔹 → 𝔹) → (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹
sub₃ : (𝔹 → 𝔹) → (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹

sub₄ o k []           ys       = []
sub₄ o k (1ᵇ∷ xs)     (1ᵇ∷ ys) = sub₄ (λ x → o (k x)) 2ᵇ∷_ xs ys
sub₄ o k (2ᵇ∷ xs)     (2ᵇ∷ ys) = sub₄ (λ x → o (k x)) 2ᵇ∷_ xs ys
sub₄ o k (1ᵇ∷ xs)     (2ᵇ∷ ys) = sub₄ o (λ x → k (1ᵇ∷ x)) xs ys
sub₄ o k (2ᵇ∷ xs)     (1ᵇ∷ ys) = sub₃ o (λ x → k (1ᵇ∷ x)) xs ys
sub₄ o k (1ᵇ∷ [])     []       = o []
sub₄ o k (1ᵇ∷ 1ᵇ∷ xs) []       = o (k (1ᵇ∷ (dec′ xs)))
sub₄ o k (1ᵇ∷ 2ᵇ∷ xs) []       = o (k (1ᵇ∷ (1ᵇ∷ xs)))
sub₄ o k (2ᵇ∷ xs)     []       = o (k (dec′ xs))

sub₃ o k []       []       = o []
sub₃ o k []       (1ᵇ∷ ys) = []
sub₃ o k []       (2ᵇ∷ ys) = []
sub₃ o k (1ᵇ∷ xs) []       = o (k (dec′ xs))
sub₃ o k (2ᵇ∷ xs) []       = o (k (1ᵇ∷ xs))
sub₃ o k (1ᵇ∷ xs) (1ᵇ∷ ys) = sub₃ o (λ x → k (1ᵇ∷ x)) xs ys
sub₃ o k (2ᵇ∷ xs) (2ᵇ∷ ys) = sub₃ o (λ x → k (1ᵇ∷ x)) xs ys
sub₃ o k (1ᵇ∷ xs) (2ᵇ∷ ys) = sub₄ (λ x → o (k x)) 2ᵇ∷_ xs ys
sub₃ o k (2ᵇ∷ xs) (1ᵇ∷ ys) = sub₃ (λ x → o (k x)) 2ᵇ∷_ xs ys

sub₂ : (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹
sub₂ k []       ys       = []
sub₂ k (1ᵇ∷ xs) []       = k (dec′ xs)
sub₂ k (2ᵇ∷ xs) []       = k (1ᵇ∷ xs)
sub₂ k (1ᵇ∷ xs) (1ᵇ∷ ys) = sub₂ (λ x → 1ᵇ∷ k x) xs ys
sub₂ k (2ᵇ∷ xs) (2ᵇ∷ ys) = sub₂ (λ x → 1ᵇ∷ k x) xs ys
sub₂ k (1ᵇ∷ xs) (2ᵇ∷ ys) = sub₄ k 2ᵇ∷_ xs ys
sub₂ k (2ᵇ∷ xs) (1ᵇ∷ ys) = sub₃ k 2ᵇ∷_ xs ys

sub₁ : (𝔹 → 𝔹) → 𝔹 → 𝔹 → 𝔹
sub₁ k  xs      []       = k xs
sub₁ k []       (1ᵇ∷ ys) = []
sub₁ k []       (2ᵇ∷ ys) = []
sub₁ k (1ᵇ∷ xs) (1ᵇ∷ ys) = sub₃ k 2ᵇ∷_ xs ys
sub₁ k (2ᵇ∷ xs) (2ᵇ∷ ys) = sub₃ k 2ᵇ∷_ xs ys
sub₁ k (2ᵇ∷ xs) (1ᵇ∷ ys) = sub₁ (λ x → 1ᵇ∷ k x) xs ys
sub₁ k (1ᵇ∷ xs) (2ᵇ∷ ys) = sub₂ (λ x → 1ᵇ∷ k x) xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
_-_ = sub₁ (λ x → x)
