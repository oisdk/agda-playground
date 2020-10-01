{-# OPTIONS --cubical --safe #-}

module Data.Nat.Fold where

open import Prelude
open import Data.Nat

foldr-ℕ : (A → A) → A → ℕ → A
foldr-ℕ f b zero = b
foldr-ℕ f b (suc n) = f (foldr-ℕ f b n)

foldr-ℕ-universal : ∀ (h : ℕ → A) f x →
                   (h zero ≡ x) →
                   (∀ n → h (suc n) ≡ f (h n)) →
                   ∀ n → h n ≡ foldr-ℕ f x n
foldr-ℕ-universal h f x base step zero = base
foldr-ℕ-universal h f x base step (suc n) = step n ; cong f (foldr-ℕ-universal h f x base step n)

foldl-ℕ-go : (A → A) → ℕ → A → A
foldl-ℕ-go f zero    x = x
foldl-ℕ-go f (suc n) x = foldl-ℕ-go f n $! f x

foldl-ℕ : (A → A) → A → ℕ → A
foldl-ℕ f x n = foldl-ℕ-go f n $! x
{-# INLINE foldl-ℕ #-}

f-comm : ∀ (f : A → A) x n → f (foldr-ℕ f x n) ≡ foldr-ℕ f (f x) n
f-comm f x zero    i = f x
f-comm f x (suc n) i = f (f-comm f x n i)

foldl-ℕ-foldr : ∀ f (x : A) n → foldr-ℕ f x n ≡ foldl-ℕ f x n
foldl-ℕ-foldr f x zero    = sym ($!-≡ (foldl-ℕ-go f zero) x)
foldl-ℕ-foldr f x (suc n) = f-comm f x n ; foldl-ℕ-foldr f (f x) n ; sym ($!-≡ (foldl-ℕ-go f (suc n)) x)

foldl-ℕ-universal : ∀ (h : ℕ → A) f x →
                   (h zero ≡ x) →
                   (∀ n → h (suc n) ≡ f (h n)) →
                   ∀ n → h n ≡ foldl-ℕ f x n
foldl-ℕ-universal h f x base step n = foldr-ℕ-universal h f x base step n ; foldl-ℕ-foldr f x n
