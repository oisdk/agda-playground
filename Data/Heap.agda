open import Relation.Binary
open import Prelude

module Data.Heap {ℓ₁} {Key : Type ℓ₁} {ℓ₂ ℓ₃} (ord : TotalOrder Key ℓ₂ ℓ₃) where

open import Data.List
open import Data.Maybe

open import Relation.Binary.Construct.LowerBound ord

open TotalOrder ord using (_≤|≥_)
open TotalOrder lb-ord hiding (_≤|≥_)

private
  variable
    u v : Level
    U : Key → Type u
    V : Key → Type v

record Heap⁺ {v} (lb : ⌊∙⌋) (V : Key → Type v) : Type (v ℓ⊔ ℓ₁ ℓ⊔ ℓ₃) where
  inductive; pattern; constructor node
  field
    key : Key
    val : V key
    bnd : lb ≤ ⌊ key ⌋
    rst : List (Heap⁺ ⌊ key ⌋ V)
open Heap⁺ public

private variable lb : ⌊∙⌋

_∪_ : Heap⁺ lb V → Heap⁺ lb V → Heap⁺ lb V
node kˣ vˣ bˣ rˣ ∪ node kʸ vʸ bʸ rʸ with kˣ ≤|≥ kʸ
... | inl x≤y = node kˣ vˣ bˣ (node kʸ vʸ x≤y rʸ ∷ rˣ)
... | inr y≤x = node kʸ vʸ bʸ (node kˣ vˣ y≤x rˣ ∷ rʸ)

merge⁺ : Heap⁺ lb V → List (Heap⁺ lb V) → Heap⁺ lb V
merge⁺ x [] = x
merge⁺ x₁ (x₂ ∷ []) = x₁ ∪ x₂
merge⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ∪ x₂) ∪ merge⁺ x₃ xs

merge : List (Heap⁺ lb V) → Maybe (Heap⁺ lb V)
merge [] = nothing
merge (x ∷ xs) = just (merge⁺ x xs)

popMin⁺ : Heap⁺ lb V → ∃ k × V k × (lb ≤ ⌊ k ⌋) × Maybe (Heap⁺ ⌊ k ⌋ V)
popMin⁺ (node k v b r) = k , v , b , merge r
