{-# OPTIONS --cubical --postfix-projections --safe #-}

module Karatsuba where

open import Prelude
open import Data.List
open import TreeFold
open import Data.Integer
open import Data.Integer.Literals
open import Data.Nat.Literals
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Literals.Number
open import Data.List.Syntax

Diff : Type
Diff = List ℤ → List ℤ

⌈⌉ : Diff
⌈⌉ = id

⌈_⌉ : ℤ → Diff
⌈_⌉ = _∷_

⌊_⌋ : Diff → List ℤ
⌊ xs ⌋ = xs []

record Parts {a} (A : Type a) : Type a where
  constructor parts
  field
    shift : ℕ
    lo hi : Diff
    out : List A
open Parts

infixl 6 _⊕_
_⊕_ : List ℤ → List ℤ → List ℤ
[]       ⊕ ys       = ys
(x ∷ xs) ⊕ []       = x ∷ xs
(x ∷ xs) ⊕ (y ∷ ys) = (x + y) ∷ (xs ⊕ ys)

pair : List ℤ → List ℤ → List (Parts ℤ)
pair []         ys       = map (λ y → parts 1 ⌈⌉ ⌈ y ⌉ []) ys
pair xs@(_ ∷ _) []       = map (λ x → parts 1 ⌈ x ⌉ ⌈⌉ []) xs
pair (x ∷ xs)   (y ∷ ys) = parts 1 ⌈ x ⌉ ⌈ y ⌉ [ x * y ] ∷ pair xs ys

pad : ℕ → Diff
pad zero    = ⌈⌉
pad (suc n) = ⌈ 0 ⌉ ∘ pad n

-- The first parameter in these functions is just used for termination checking.
mutual
  infixl 7 ⟨_⟩_⊛_
  ⟨_⟩_⊛_ : ℕ → List ℤ → List ℤ → List ℤ
  ⟨ n ⟩ []             ⊛ _              = []
  ⟨ n ⟩    (_ ∷ _)     ⊛ []             = []
  ⟨ n ⟩    (x ∷ [])    ⊛ ys@(_ ∷ _)     = map (x *_) ys
  ⟨ n ⟩ xs@(_ ∷ _ ∷ _) ⊛    (y ∷ [])    = map (y *_) xs
  ⟨ n ⟩ xs@(_ ∷ _ ∷ _) ⊛ ys@(_ ∷ _ ∷ _) = treeFold1 ⟨ n ⟩_◆_ (pair xs ys) .out

  ⟨_⟩_◆_ : ℕ → Parts ℤ → Parts ℤ → Parts ℤ
  (⟨ n ⟩ xs ◆ ys) .shift = xs .shift ℕ.+ ys .shift
  (⟨ n ⟩ xs ◆ ys) .lo = xs .lo ∘ ys .lo
  (⟨ n ⟩ xs ◆ ys) .hi = xs .hi ∘ ys .hi
  (⟨ zero  ⟩ parts m x0 y0 z0 ◆ parts n x1 y1 z2) .out = [] -- should not happen
  (⟨ suc t ⟩ parts m x0 y0 z0 ◆ parts n x1 y1 z2) .out = pad m (pad m z2 ⊕ z1) ⊕ z0
    where
    z1 : List ℤ
    z1 = ⟨ t ⟩ (⌊ x0 ⌋ ⊕ ⌊ x1 ⌋) ⊛ (⌊ y0 ⌋ ⊕ ⌊ y1 ⌋) ⊕ (map negate z0 ⊕ map negate z2)

_⊛_ : List ℤ → List ℤ → List ℤ
xs ⊛ ys = ⟨ length xs ℕ.+ length ys ⟩ xs ⊛ ys

_ : [ 2 , 5 ] ⊛ [ 1 , 1 ] ≡ [ 2 , 7 , 5 ]
_ = refl
