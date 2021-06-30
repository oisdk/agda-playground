{-# OPTIONS --cubical --safe --guardedness #-}

module Data.PolyP.Composition where

open import Function hiding (_⟨_⟩_)
open import Data.Sum
open import Data.Sigma
open import Level hiding (Type) renaming (Type to Type)
open import Data.Unit
open import Data.Nat
open import Data.Vec
open import Data.Empty
open import WellFounded
open import Literals.Number
open import Data.Fin.Indexed.Literals
open import Data.Fin.Indexed.Properties
open import Data.Fin.Indexed
open import Data.Nat.Literals
open import Data.Maybe

open import Data.PolyP.Universe

infixr 9 _⊚_

_⇑_ : Fin (suc n) → Functor n → Functor (suc n)
i ⇑ (! j) = ! (insert i j)
i ⇑ (x ⊕ y) = i ⇑ x ⊕ i ⇑ y
i ⇑ (x ⊗ y) = i ⇑ x ⊗ i ⇑ y
i ⇑ μ⟨ x ⟩ = μ⟨ fs i ⇑ x ⟩
i ⇑ ⓪ = ⓪
i ⇑ ① = ①

⇓ : Functor n → Functor (suc n)
⇓ (! x) = ! (weaken x)
⇓ (x ⊕ y) = ⇓ x ⊕ ⇓ y
⇓ (x ⊗ y) = ⇓ x ⊗ ⇓ y
⇓ μ⟨ x ⟩ = μ⟨ f0 ⇑ x ⟩
⇓ ⓪ = ⓪
⇓ ① = ①

substAt : Fin (suc n) → Functor (suc n) → Functor n → Functor n
substAt i (! j)     xs = maybe xs ! (j \\ i)
substAt i (ys ⊕ zs) xs = substAt i ys xs ⊕ substAt i zs xs
substAt i (ys ⊗ zs) xs = substAt i ys xs ⊗ substAt i zs xs
substAt i μ⟨ ys ⟩   xs = μ⟨ substAt (fs i) ys (f0 ⇑ xs) ⟩
substAt i ⓪         xs = ⓪
substAt i ①         xs = ①

_⊚_ : Functor (suc n) → Functor n → Functor n
_⊚_ = substAt f0
