{-# OPTIONS --cubical --postfix-projections #-}

module Karatsuba where

open import Prelude
open import Data.List
open import TreeFold
open import Data.Integer
open import Data.Integer.Literals
open import Data.Nat.Literals
import Data.Nat as ℕ
open import Literals.Number

data Tree {a} (A : Type a) : Type a where
  empt : Tree A
  leaf : A → Tree A
  _⊗_ : Tree A → Tree A → Tree A

toList : Tree A → List A
toList xs = go xs []
  where
  go : Tree A → List A → List A
  go empt ks = ks
  go (leaf x) ks = x ∷ ks
  go (ls ⊗ rs) ks = go ls (go rs ks)

record Parts {a} (A : Type a) : Type a where
  constructor parts
  field
    shift : ℕ
    lo : Tree A
    hi : Tree A
    out : List A
open Parts

infixl 6 _⊕_
_⊕_ : List ℤ → List ℤ → List ℤ
[] ⊕ ys = ys
(x ∷ xs) ⊕ [] = x ∷ xs
(x ∷ xs) ⊕ (y ∷ ys) = (x + y) ∷ (xs ⊕ ys)

pair : List ℤ → List ℤ → List (Parts ℤ)
pair [] ys = map (λ y → parts 1 (leaf 0) (leaf y) (0 ∷ [])) ys
pair xs [] = map (λ x → parts 1 (leaf x) (leaf 0) (0 ∷ [])) xs
pair (x ∷ xs) (y ∷ ys) = parts 1 (leaf x) (leaf y) (x * y ∷ []) ∷ pair xs ys

mutual
  infixl 7 ⟨_⟩_⊛_
  ⟨_⟩_⊛_ : ℕ → List ℤ → List ℤ → List ℤ
  ⟨ n ⟩ [] ⊛ _ = []
  ⟨ n ⟩ _ ⊛ [] = []
  ⟨ n ⟩ (x ∷ []) ⊛ ys = map (x *_) ys
  ⟨ n ⟩ xs ⊛ (y ∷ []) = map (y *_) xs
  ⟨ n ⟩ xs ⊛ ys = treeFold ⟨ n ⟩_◆_ (parts 0 empt empt []) (pair xs ys) .out

  ⟨_⟩_◆_ : ℕ → Parts ℤ → Parts ℤ → Parts ℤ
  (⟨ n ⟩ xs ◆ ys) .shift = xs .shift ℕ.+ ys .shift
  (⟨ n ⟩ xs ◆ ys) .lo = xs .lo ⊗ ys .lo
  (⟨ n ⟩ xs ◆ ys) .hi = xs .hi ⊗ ys .hi
  (⟨ zero ⟩ parts m x0 y0 z0 ◆ parts n x1 y1 z2) .out = []
  (⟨ suc t ⟩ parts m x0 y0 z0 ◆ parts n x1 y1 z2) .out = (replicate 0 (2 ℕ.* m) ++ z2) ⊕ (replicate 0 m ++ z1) ⊕ z0
    where
    z1 : List ℤ
    z1 = ⟨ t ⟩ (toList x1 ⊕ toList x0) ⊛ (toList y1 ⊕ toList y0) ⊕ map negate z2 ⊕ map negate z0

_⊛_ : List ℤ → List ℤ → List ℤ
xs ⊛ ys = ⟨ length xs ℕ.+ length ys ⟩ xs ⊛ ys


e : List ℤ
e = (2 ∷ 5 ∷ []) ⊛ (1 ∷ 1 ∷ [])

_ : e ≡ 2 ∷ 7 ∷ 5 ∷ 0 ∷ []
_ = refl
