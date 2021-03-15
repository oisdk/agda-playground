{-# OPTIONS --cubical --safe --guardedness #-}

module Data.PolyP.Currying where

open import Prelude hiding (_⟨_⟩_)
open import Data.Vec.Iterated

open import Data.PolyP.Universe

Curriedⁿ : ℕ → Type₁
Curriedⁿ zero    = Type₀
Curriedⁿ (suc n) = Type₀ → Curriedⁿ n

_~_ : ∀ {n} → (Params n → Type₀) → Curriedⁿ n
_~_ {n = zero}  f = f []
_~_ {n = suc n} f A = _~_ {n = n} (f ∘ (A ∷_))
