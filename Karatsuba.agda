{-# OPTIONS --cubical --postfix-projections --safe #-}

module Karatsuba where

open import Prelude

open import Data.List
open import Data.List.Syntax

open import TreeFold

open import Data.Integer

import Data.Nat as ℕ

open import Literals.Number
open import Data.Integer.Literals

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
    pz lo hi : Diff A
    out : List A
open K

infixl 6 _⊕_
_⊕_ : List ℤ → List ℤ → List ℤ
[]       ⊕ ys       = ys
xs       ⊕ []       = xs
(x ∷ xs) ⊕ (y ∷ ys) = (x + y) ∷ (xs ⊕ ys)

pair : List ℤ → List ℤ → List (K ℤ)
pair []       ys       = map (λ y → k ⌈ 0 ⌉ ⌈⌉ ⌈ y ⌉ []) ys
pair xs       []       = map (λ x → k ⌈ 0 ⌉ ⌈ x ⌉ ⌈⌉ []) xs
pair (x ∷ xs) (y ∷ ys) = k ⌈ 0 ⌉ ⌈ x ⌉ ⌈ y ⌉ [ x * y ] ∷ pair xs ys

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
  (⟨ _     ⟩ xs           ◆ ys          ) .pz  = xs .pz ∘ ys .pz
  (⟨ _     ⟩ xs           ◆ ys          ) .lo  = xs .lo ∘ ys .lo
  (⟨ _     ⟩ xs           ◆ ys          ) .hi  = xs .hi ∘ ys .hi
  (⟨ zero  ⟩ _            ◆ _           ) .out = [] -- should not happen
  (⟨ suc t ⟩ k p x₀ y₀ z₀ ◆ k _ x₁ y₁ z₂) .out = p (p z₂ ⊕ z₁) ⊕ z₀
    where
    z₁ = ⟨ t ⟩ (⌊ x₀ ⌋ ⊕ ⌊ x₁ ⌋) ⊛ (⌊ y₀ ⌋ ⊕ ⌊ y₁ ⌋) ⊕
              (map negate z₀ ⊕ map negate z₂)

_⊛_ : List ℤ → List ℤ → List ℤ
xs ⊛ ys = ⟨ length xs ℕ.+ length ys ⟩ xs ⊛ ys

_ : [ 2 , 5 ] ⊛ [ 1 , 1 ] ≡ [ 2 , 7 , 5 ]
_ = refl
