module Data.Set.Syntax where

open import Data.Set.Definition
-- open import Data.Nat
open import Prelude

-- Vec⁺ : Type a → ℕ → Type a
-- Vec⁺ A zero    = A
-- Vec⁺ A (suc n) = A × Vec⁺ A n

-- ⟅_⟆ : ∀ {n} → Vec⁺ A n → 𝒦 A
-- ⟅_⟆ {n = zero}  x        = x ∷ ∅
-- ⟅_⟆ {n = suc n} (x , xs) = x ∷ ⟅ xs ⟆

infixr 4 _,_
data SetBuilder (A : Type a) : Type a where
  sing : A → SetBuilder A
  _,_ : A → SetBuilder A → SetBuilder A

infixl 6 _⟆
_⟆ : A → SetBuilder A
_⟆ = sing

infixr 4 ⟅_
⟅_ : SetBuilder A → 𝒦 A
⟅ (sing x) = x ∷ ∅
⟅ x , xs = x ∷ (⟅ xs)

