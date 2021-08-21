\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Weighted.Definition {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels

infixr 5 _◃_∷_
\end{code}
%<*list-part>
\begin{code}
data Weighted (A : Type a) : Type (a ℓ⊔ ℓ) where
  []     :  Weighted A
  _◃_∷_  :  (p : 𝑅) (x : A) (xs : Weighted A) → Weighted A
\end{code}
%</list-part>
%<*trunc>
\begin{code}
  trunc : isSet (Weighted A)
\end{code}
%</trunc>
%<*quots>
\begin{code}
  com  : ∀ p x q y xs  → p ◃ x ∷ q ◃ y ∷ xs  ≡ q ◃ y ∷ p ◃ x ∷ xs
  dup  : ∀ p q x xs    → p ◃ x ∷ q ◃ x ∷ xs  ≡ p + q ◃ x ∷ xs
  del  : ∀ x xs        → 0# ◃ x ∷ xs         ≡ xs
\end{code}
%</quots>
