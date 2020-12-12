{-# OPTIONS --cubical --safe #-}

module Data.Vec.Iterated where

open import Prelude hiding (⊤)
open import Data.Unit.UniversePolymorphic
open import Data.List using (List; length)
import Data.List as List

private
  variable
    n m : ℕ

mutual
  Vec :  Type a → ℕ → Type a
  Vec A zero     = Vec⁰
  Vec A (suc n)  = Vec⁺ A n

  record Vec⁰ {a} : Type a where
    constructor []

  infixr 5 _∷_
  record Vec⁺ {a} (A : Type a) (n : ℕ) : Type a where
    eta-equality
    inductive
    constructor _∷_
    field
      head : A
      tail : Vec A n

open Vec⁺ public

foldrP : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldrP {n = zero} P f b _         = b
foldrP {n = suc n} P f b (x ∷ xs) = f x (foldrP P f b xs)

foldl : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldl {n = zero } P f b _ = b
foldl {n = suc n} P f b (x ∷ xs) = foldl (P ∘ suc) f (f x b) xs

module _ (f : A → B → B) (e : B) where
  foldr′ : Vec A n → B
  foldr′ {n = zero } xs = e
  foldr′ {n = suc n} (x ∷ xs) = f x (foldr′ xs)

foldl′ : (A → B → B) → B → Vec A n → B
foldl′ {n = zero}  f b xs = b
foldl′ {n = suc n} f b (x ∷ xs) = foldl′ f (f x b) xs

vecFromList : (xs : List A) → Vec A (length xs)
vecFromList List.[] = []
vecFromList (x List.∷ xs) = x ∷ vecFromList xs

vecToList : Vec A n → List A
vecToList = foldr′ List._∷_ List.[]
