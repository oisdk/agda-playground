{-# OPTIONS --cubical --safe --guardedness --postfix-projections #-}

module Codata.Stream where

open import Prelude
open import Data.List using (List; _∷_; [])
open import Data.List.Kleene
import Data.List.Kleene.Membership as Kleene
open import Data.Fin

infixr 5 _◃_
record Stream (A : Type a) : Type a where
  constructor _◃_
  coinductive
  field
    head  : A
    tail  : Stream A
open Stream public

Stream′ : Type a → Type a
Stream′ A = ℕ → A

_!_ : Stream A → Stream′ A
xs ! zero  = xs .head
xs ! suc n = xs .tail ! n

tabulate : Stream′ A → Stream A
tabulate xs .head = xs zero
tabulate xs .tail = tabulate (xs ∘ suc)

linv : (xs : Stream A) → tabulate (xs !_) ≡ xs
linv xs i .head = xs .head
linv xs i .tail = linv (xs .tail) i

rinv : (xs : Stream′ A) → (tabulate xs !_) ≡ xs
rinv xs i zero    = xs zero
rinv xs i (suc n) = rinv (xs ∘ suc) i n

stream : Stream A ⇔ Stream′ A
stream .fun = _!_
stream .inv = tabulate
stream .rightInv = rinv
stream .leftInv = linv



-- infixr 5 _∈_
-- _∈_ : A → Stream A → Type _
-- x ∈ xs = fiber xs x

-- toList : ℕ → Stream A → List A
-- toList zero xs = []
-- toList (suc n) xs = xs zero ∷ toList n (xs ∘ suc)

-- mutual
--   concat⋆ : A ⋆ → Stream (A ⁺) → Stream A
--   concat⋆ []    xs = concat⁺ (xs zero) (xs ∘ suc)
--   concat⋆ (∹ x) xs = concat⁺ x xs

--   concat⁺ : A ⁺ → Stream (A ⁺) → Stream A
--   concat⁺ x xs zero    = x .head
--   concat⁺ x xs (suc n) = concat⋆ (x .tail) xs n

-- concat : Stream (A ⁺) → Stream A
-- concat xs = concat⁺ (xs zero) (xs ∘ suc)

-- infixr 5 _∈²_
-- _∈²_ : A → Stream (A ⁺) → Type _
-- x ∈² xs = ∃[ n ] x Kleene.∈⁺ xs n

-- mutual
--   ◇++⋆ : ∀ (x : A) y ys → x Kleene.∈⋆ y → x ∈ concat⋆ y ys
--   ◇++⋆ x (∹ y) ys x∈y = ◇++⁺ x y ys x∈y

--   ◇++⁺ : ∀ (x : A) y ys → x Kleene.∈⁺ y → x ∈ concat⁺ y ys
--   ◇++⁺ x y ys (f0 , x∈y) = zero , x∈y
--   ◇++⁺ x y ys (fs n , x∈y) = let m , p = ◇++⋆ x (y .tail) ys (n , x∈y) in suc m , p

-- mutual
--   ++◇⋆ : ∀ (x : A) y ys → x ∈ concat ys → x ∈ concat⋆ y ys
--   ++◇⋆ x [] ys x∈ys = x∈ys
--   ++◇⋆ x (∹ y) ys x∈ys = ++◇⁺ x y ys x∈ys

--   ++◇⁺ : ∀ (x : A) y ys → x ∈ concat ys → x ∈ concat⁺ y ys
--   ++◇⁺ x y ys x∈ys = let n , p = ++◇⋆ x (y .tail) ys x∈ys in suc n , p

-- concat-∈ : ∀ (x : A) xs → x ∈² xs → x ∈ concat xs
-- concat-∈ x xs (zero  , x∈xs) = ◇++⁺ x (xs zero) (xs ∘ suc) x∈xs
-- concat-∈ x xs (suc n , x∈xs) = ++◇⁺ x (xs zero) (xs ∘ suc) (concat-∈ x (xs ∘ suc) (n , x∈xs))
