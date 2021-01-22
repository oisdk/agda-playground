{-# OPTIONS --without-K --safe #-}

module Data.Vec.Iterated where

open import Data.Unit.UniversePolymorphic
open import Level
open import Data.Nat.Base
open import Function

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

foldr : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldr {n = zero} P f b _         = b
foldr {n = suc n} P f b (x ∷ xs) = f x (foldr P f b xs)

foldl : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldl {n = zero } P f b _ = b
foldl {n = suc n} P f b (x ∷ xs) = foldl (P ∘ suc) f (f x b) xs

foldlN : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P (suc n) → P n) →
          P n →
          Vec A n → P zero
foldlN P f b xs = foldr (λ n → P n → P zero) (λ x k xs → k (f x xs)) id xs b

module _ (f : A → B → B) (e : B) where
  foldr′ : Vec A n → B
  foldr′ {n = zero } xs = e
  foldr′ {n = suc n} (x ∷ xs) = f x (foldr′ xs)

foldl′ : (A → B → B) → B → Vec A n → B
foldl′ {n = zero}  f b xs = b
foldl′ {n = suc n} f b (x ∷ xs) = foldl′ f (f x b) xs

-- vecFromList : (xs : List A) → Vec A (length xs)
-- vecFromList List.[] = []
-- vecFromList (x List.∷ xs) = x ∷ vecFromList xs

-- vecToList : Vec A n → List A
-- vecToList = foldr′ List._∷_ List.[]

open import Data.Fin.Indexed

infixl 4 lookup
lookup : Fin n → Vec A n → A
lookup f0     (x ∷ _ ) = x
lookup (fs i) (_ ∷ xs) = lookup i xs

syntax lookup i xs = xs [ i ]

infixl 4 replace
replace : Fin n → Vec A n → A → Vec A n
replace f0     (_ ∷ xs) x = x ∷ xs
replace (fs i) (x ∷ xs) y = x ∷ replace i xs y

syntax replace i xs x = xs [ i ]≔ x
