{-# OPTIONS --cubical --safe #-}

module Data.List.Base where

open import Prelude

private
  module DisplayDefinition where
    data List (A : Type a) : Type a where
      []   : List A
      _∷_  : A → List A → List A

open import Agda.Builtin.List using (List; _∷_; []) public
open import Data.Fin

foldr : (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

infixr 5 _++_
_++_ : List A → List A → List A
xs ++ ys = foldr _∷_ ys xs

length : List A → ℕ
length = foldr (const suc) zero

infixl 6 _!_
_!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) ! f0 = x
(x ∷ xs) ! fs i = xs ! i

tabulate : ∀ n → (Fin n → A) → List A
tabulate zero f = []
tabulate (suc n) f = f f0 ∷ tabulate n (f ∘ fs)

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f = foldr (λ x ys → f x ++ ys) []

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
