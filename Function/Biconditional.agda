{-# OPTIONS --cubical --safe #-}

module Function.Biconditional where

open import Level
open import Relation.Binary
open import Path as ≡ using (_;_; cong)
open import Function

infix 4 _↔_
record _↔_ {a b} (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor _iff_
  field
    fun : A → B
    inv : B → A
open _↔_ public

sym-↔ : (A ↔ B) → (B ↔ A)
fun (sym-↔ A↔B) = inv A↔B
inv (sym-↔ A↔B) = fun A↔B

refl-↔ : A ↔ A
fun refl-↔ = id
inv refl-↔ = id

trans-↔ : A ↔ B → B ↔ C → A ↔ C
fun (trans-↔ A↔B B↔C) = fun B↔C ∘ fun A↔B
inv (trans-↔ A↔B B↔C) = inv A↔B ∘ inv B↔C
