{-# OPTIONS --cubical --safe --guardedness #-}

module Data.PolyP.Types where

open import Function hiding (_⟨_⟩_)
open import Data.Sum
open import Data.Sigma
open import Level hiding (Type) renaming (Type₀ to Type)
open import Data.Unit
open import Data.Nat
open import Data.Empty
open import WellFounded
open import Literals.Number
open import Data.Fin.Indexed.Literals
open import Data.Fin.Indexed.Properties
open import Data.Fin.Indexed
open import Data.Nat.Literals
open import Data.Maybe

open import Data.PolyP.Universe
open import Data.PolyP.Composition
open import Data.PolyP.Currying
open import Data.PolyP.RecursionSchemes

LIST : ∀ {n} → Functor (suc n)
LIST = μ⟨ ① ⊕ ! (fs f0) ⊗ ! f0 ⟩

-- The free near-semiring
FOREST : Functor 1
FOREST = μ⟨ LIST ⊚ (① ⊕ ! (fs f0) ⊗ ! f0) ⟩

-- Lists of lists
LEVELS : Functor 1
LEVELS = μ⟨ ① ⊕ ! (fs f0) ⊗ ! f0 ⟩ ⊚ μ⟨ ① ⊕ ! (fs f0) ⊗ ! f0 ⟩

-- The free monad
FREE : Functor 1 → Functor 1
FREE f = μ⟨ ! (fs f0) ⊕ f0 ⇑ f ⟩

COFREE : Functor 1 → Functor 1
COFREE f = μ⟨ ! (fs f0) ⊗ f0 ⇑ f ⟩

ROSE : Functor 1
ROSE = μ⟨ ! (fs f0) ⊗ f0 ⇑ LIST ⟩

module _ {A B : Type} where
  FOLDR : (A → B → B) → B → ⟦ LIST ⟧ ~ A → B
  FOLDR f b = cata (const b ▿ uncurry f)

open import Data.List
open import Data.List.Properties
open import Function.Isomorphism
open import Path

pattern _∷′_ x xs  = ⟨ inr (x , xs) ⟩
pattern []′        = ⟨ inl tt ⟩

generic-list : List A ⇔ ⟦ LIST ⟧ ~ A
generic-list .fun       = foldr  _∷′_  []′
generic-list .inv       = FOLDR  _∷_   []
generic-list .leftInv   = list-elim  _      (λ      x     xs     p    i → x ∷   p i)          λ   i → []
generic-list .rightInv  = elim       _ λ {  (inr (  x ,   xs ,   p))  i → x ∷′  p i   ; (inl  _)  i → []′ }

open import Data.Vec

STREAM : Type → Type
STREAM A = ν (! (fs f0) ⊗ ! f0) ~ A

nats : ℕ → STREAM ℕ
nats n .unfold = n , nats (suc n)
