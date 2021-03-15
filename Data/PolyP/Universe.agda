{-# OPTIONS --cubical --guardedness --safe #-}

module Data.PolyP.Universe where

open import Prelude hiding (_⟨_⟩_)
open import Data.Vec.Iterated
open import Data.Fin.Indexed

--------------------------------------------------------------------------------
--
--  The Universe of functors we're interested in.
--
--------------------------------------------------------------------------------
data Functor (n : ℕ) : Type₀ where
  !     : Fin n → Functor n
  _⊕_   : (F G : Functor n) → Functor n
  _⊗_   : (F G : Functor n) → Functor n
  μ⟨_⟩  : Functor (suc n) → Functor n
  ⓪     : Functor n
  ①     : Functor n

infixl 6 _⊕_
infixl 7 _⊗_

Params : ℕ → Type₁
Params = Vec Type₀

variable
  n m k : ℕ
  F G : Functor n
  As Bs : Params n

---------------------------------------------------------------------------------
--
-- Interpretation
--
---------------------------------------------------------------------------------

mutual
  ⟦_⟧ : Functor n → Params n → Type₀
  ⟦ ! i     ⟧ xs = xs [ i ]
  ⟦ F ⊕  G  ⟧ xs = ⟦ F ⟧ xs ⊎  ⟦ G ⟧ xs
  ⟦ F ⊗  G  ⟧ xs = ⟦ F ⟧ xs ×  ⟦ G ⟧ xs
  ⟦ μ⟨ F ⟩  ⟧ xs = μ F xs
  ⟦ ⓪       ⟧ xs = ⊥
  ⟦ ①       ⟧ xs = ⊤
  record μ (F : Functor (suc n)) (As : Params n) : Type₀ where
    inductive; constructor ⟨_⟩
    field unwrap : ⟦ F ⟧ (μ F As ∷ As)
open μ public
