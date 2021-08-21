{-# OPTIONS --cubical --safe #-}

module Control.Monad.Weighted.Functor.TypeDef where

open import Level

data 𝔚-F {r w a p} (R : Type r) (W : Type w) (A : Type a) (P : W → Type p) : Type (r ℓ⊔ a ℓ⊔ p ℓ⊔ w) where
  [] : 𝔚-F R W A P
  _◃_∷_⟨_⟩ : ∀ (w : R) (x : A) (xs : W) (P⟨xs⟩ : P xs) → 𝔚-F R W A P
