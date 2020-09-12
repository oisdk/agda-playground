{-# OPTIONS --cubical --safe #-}

module Data.Vec.Iterated where

open import Prelude hiding (⊤)
open import Data.Unit.UniversePolymorphic
open import Data.List using (List; _∷_; []; length)

private
  variable
    n m : ℕ
Vec :  Type a →
       ℕ →
       Type a
Vec A zero     = ⊤
Vec A (suc n)  = A × Vec A n

foldr : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldr {n = zero} P f b _         = b
foldr {n = suc n} P f b (x , xs) = f x (foldr P f b xs)

foldl : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldl {n = zero } P f b _ = b
foldl {n = suc n} P f b (x , xs) = foldr (P ∘ suc) f (f x b) xs

foldr′ : (A → B → B) → B → Vec A n → B
foldr′ f = foldr (const _) (λ x xs → f x xs)

foldl′ : (A → B → B) → B → Vec A n → B
foldl′ f = foldl (const _) (λ x xs → f x xs)

vecFromList : (xs : List A) → Vec A (length xs)
vecFromList [] = tt
vecFromList (x ∷ xs) = x , vecFromList xs

vecToList : Vec A n → List A
vecToList = foldr′ _∷_ []
