{-# OPTIONS --safe --without-K #-}

module Level where

open import Agda.Primitive
  using (Level)
  renaming ( _⊔_ to _ℓ⊔_
           ; lzero to ℓzero
           ; lsuc  to ℓsuc )
  public

Type : (ℓ : Level) → Set (ℓsuc ℓ)
Type ℓ = Set ℓ

Type₀ = Type ℓzero
Type₁ = Type (ℓsuc ℓzero)
Type₂ = Type (ℓsuc (ℓsuc ℓzero))
Type₃ = Type (ℓsuc (ℓsuc (ℓsuc ℓzero)))

variable
  a b c : Level
  A  : Type a
  B  : Type b
  C  : Type c
