{-# OPTIONS --cubical --safe #-}

module Data.Vec.Inductive where

open import Prelude
open import Data.List using (List; _∷_; []; length)

private
  variable
    n m : ℕ

infixr 5 _∷_
data Vec (A : Type a) : ℕ → Type a where
  [] : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

foldr : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldr P f b [] = b
foldr P f b (x ∷ xs) = f x (foldr P f b xs)

foldl : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldl P f b [] = b
foldl P f b (x ∷ xs) = foldl (P ∘ suc) f (f x b) xs

foldr′ : (A → B → B) → B → Vec A n → B
foldr′ f = foldr (const _) (λ x xs → f x xs)

foldl′ : (A → B → B) → B → Vec A n → B
foldl′ f = foldl (const _) (λ x xs → f x xs)

vecFromList : (xs : List A) → Vec A (length xs)
vecFromList [] = []
vecFromList (x ∷ xs) = x ∷ vecFromList xs

vecToList : Vec A n → List A
vecToList [] = []
vecToList (x ∷ xs) = x ∷ vecToList xs
