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
open import Data.Maybe using (maybe)

Diff : Type a → Type a
Diff A = List A → List A

⌈⌉ : Diff A
⌈⌉ = id

⌈_⌉ : A → Diff A
⌈_⌉ = _∷_

⌊_⌋ : Diff A → List A
⌊ xs ⌋ = xs []

record K (A : Type a) : Type a where
  constructor k
  field
    shift : ℕ → ℕ
    lo hi : Diff A
    out : List A
open K

infixl 6 _⊕_
_⊕_ : List ℤ → List ℤ → List ℤ
[]       ⊕ ys       = ys
xs       ⊕ []       = xs
(x ∷ xs) ⊕ (y ∷ ys) = (x + y) ∷ (xs ⊕ ys)

pair : List ℤ → List ℤ → List (K ℤ)
pair []         ys       = map (λ y → k suc ⌈⌉ ⌈ y ⌉ []) ys
pair xs         []       = map (λ x → k suc ⌈ x ⌉ ⌈⌉ []) xs
pair (x ∷ xs)   (y ∷ ys) = k suc ⌈ x ⌉ ⌈ y ⌉ [ x * y ] ∷ pair xs ys

pad : ℕ → Diff ℤ 
pad zero    = ⌈⌉
pad (suc n) = ⌈ 0 ⌉ ∘ pad n

-- The first parameter in these functions is just used for termination checking.
mutual
  infixl 7 ⟨_⟩_⊛_
  ⟨_⟩_⊛_ : ℕ → List ℤ → List ℤ → List ℤ
  ⟨ n ⟩ []       ⊛ _        = []
  ⟨ n ⟩ _        ⊛ []       = []
  ⟨ n ⟩ (x ∷ []) ⊛ ys       = map (x *_) ys
  ⟨ n ⟩ xs       ⊛ (y ∷ []) = map (y *_) xs
  ⟨ n ⟩ xs       ⊛ ys       = maybe [] out (treeFoldMay ⟨ n ⟩_◆_ (pair xs ys))

  ⟨_⟩_◆_ : ℕ → K ℤ → K ℤ → K ℤ
  (⟨ _     ⟩ xs           ◆ ys          ) .shift = xs .shift ∘ ys .shift
  (⟨ _     ⟩ xs           ◆ ys          ) .lo    = xs .lo ∘ ys .lo
  (⟨ _     ⟩ xs           ◆ ys          ) .hi    = xs .hi ∘ ys .hi
  (⟨ zero  ⟩ k m x0 y0 z0 ◆ k n x1 y1 z2) .out   = [] -- should not happen
  (⟨ suc t ⟩ k m x0 y0 z0 ◆ k n x1 y1 z2) .out   = let m′ = m 0 in pad m′ (pad m′ z2 ⊕ z1) ⊕ z0
    where
    z1 : List ℤ
    z1 = ⟨ t ⟩ (⌊ x0 ⌋ ⊕ ⌊ x1 ⌋) ⊛ (⌊ y0 ⌋ ⊕ ⌊ y1 ⌋) ⊕ (map negate z0 ⊕ map negate z2)

_⊛_ : List ℤ → List ℤ → List ℤ
xs ⊛ ys = ⟨ length xs ℕ.+ length ys ⟩ xs ⊛ ys

_ : [ 2 , 5 ] ⊛ [ 1 , 1 ] ≡ [ 2 , 7 , 5 ]
_ = refl
