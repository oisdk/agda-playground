{-# OPTIONS --without-K --safe #-}

module Data.List.Base where

open import Level
open import Agda.Builtin.List using (List; _∷_; []) public
open import Data.Nat.Base
open import Function
open import Strict
open import Data.Maybe using (Maybe; just; nothing; maybe)

foldr : (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

foldrMay : (A → A → A) → List A → Maybe A
foldrMay f = foldr (λ x → just ∘ maybe x (f x)) nothing

foldl : (B → A → B) → B → List A → B
foldl f b [] = b
foldl f b (x ∷ xs) = foldl f (f b x) xs

foldl′ : (B → A → B) → B → List A → B
foldl′ f b [] = b
foldl′ f b (x ∷ xs) = let! z =! f b x in! foldl′ f z xs

foldr′ : (A → B → B) → B → List A → B
foldr′ f b [] = b
foldr′ f b (x ∷ xs) = f x $! foldr′ f b xs

infixr 5 _++_
_++_ : List A → List A → List A
xs ++ ys = foldr _∷_ ys xs

length : List A → ℕ
length = foldr (const suc) zero

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f = foldr (λ x ys → f x ++ ys) []

catMaybes : (A → Maybe B) → List A → List B
catMaybes f = foldr (λ x xs → maybe xs (_∷ xs) (f x)) []

map : (A → B) → List A → List B
map f = foldr (λ x xs → f x ∷ xs) []

take : ℕ → List A → List A
take zero _ = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

_⋯_ : ℕ → ℕ → List ℕ
_⋯_ n = go n
  where
  go″ : ℕ → ℕ → List ℕ
  go′ : ℕ → ℕ → List ℕ

  go″ n zero = []
  go″ n (suc m) = go′ (suc n) m

  go′ n m = n ∷ go″ n m

  go : ℕ → ℕ → List ℕ
  go zero = go′ n
  go (suc n) zero = []
  go (suc n) (suc m) = go n m

replicate : A → ℕ → List A
replicate {A = A} x = go
  where
  go : ℕ → List A
  go zero = []
  go (suc n) = x ∷ go n
