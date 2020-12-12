{-# OPTIONS --cubical --safe --postfix-projections #-}

module Function.Injective.Base where

open import Level
open import Path
open import Data.Sigma

Injective : (A → B) → Type _
Injective f = ∀ x y → (f⟨x⟩≡f⟨y⟩ : f x ≡ f y) → x ≡ y

infixr 0 _↣_
_↣_ : Type a → Type b → Type (a ℓ⊔ b)
A ↣ B = Σ[ f ⦂ (A → B) ] Injective f
refl-↣ : A ↣ A
refl-↣ .fst x = x
refl-↣ .snd x y x≡y = x≡y
