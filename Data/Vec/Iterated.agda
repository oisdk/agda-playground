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
    eta-equality
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

_++_ : Vec A n → Vec A m → Vec A (n + m)
_++_ {n = zero} []  = id
_++_ {n = suc n} (x ∷ xs) ys = x ∷ (xs ++ ys)

open import Data.Sigma

split : Vec A (n + m) → Vec A n × Vec A m
split {n = zero} xs .fst = []
split {n = zero} xs .snd = xs
split {n = suc n} xs .fst .head = xs .head
split {n = suc n} xs .fst .tail = split (xs .tail) .fst
split {n = suc n} xs .snd = split (xs .tail) .snd

foldr : ∀ {p} (P : ℕ → Type p) →
          (∀ {n} → A → P n → P (suc n)) →
          P zero →
          Vec A n → P n
foldr {n = zero} P f b _         = b
foldr {n = suc n} P f b (x ∷ xs) = f x (foldr P f b xs)

vmap : (A → B) → Vec A n → Vec B n
vmap f = foldr (Vec _) (_∷_ ∘ f) []

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
lookup f0     = head
lookup (fs i) xs = lookup i (tail xs)

syntax lookup i xs = xs [ i ]

infixl 4 replace
replace : Fin n → A → Vec A n → Vec A n
replace f0     x xs .head = x
replace f0     x xs .tail = xs .tail
replace (fs i) x xs .head = xs .head
replace (fs i) x xs .tail = replace i x (xs .tail)

syntax replace i x xs = xs [ i ]≔ x
