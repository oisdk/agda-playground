{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Relation.Binary
open import Algebra.Monus
open import Level

module Data.MonoidalHeap.Monad {s} {𝑆 : Type s} (monus : TMAPOM 𝑆) where

open TMAPOM monus

open import Prelude
open import Data.List using (List; _∷_; []; foldr; _++_)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ

𝒮 : Type s
𝒮 = 𝑆 → 𝑆

⟦_⇑⟧ : 𝑆 → 𝒮
⟦_⇑⟧ = _∙_

⟦_⇓⟧ : 𝒮 → 𝑆
⟦ x ⇓⟧ = x ε

infixl 10 _⊙_
_⊙_ : (𝑆 → A) → 𝑆 → 𝑆 → A
f ⊙ x = λ y → f (x ∙ y)

mutual
  data Node (V : 𝑆 → Type a) : Type (a ℓ⊔ s) where
    leaf : V ε → Node V
    _⋊_ : (w : 𝑆) → Heap (V ⊙ w) → Node V

  Heap : (𝑆 → Type a) → Type (a ℓ⊔ s)
  Heap V = List (Node V)

private
  variable
    v : Level
    V : 𝑆 → Type v

Root : (𝑆 → Type v) → Type _
Root V = ∃ w × Heap (V ⊙ w)

partition : Heap V → List (V ε) × List (Root V)
partition = foldr f ([] , [])
  where
    f : Node V → List (V ε) × List (∃ w × Heap (V ⊙ w)) → List (V ε) × List (∃ w × Heap (V ⊙ w))
    f (leaf x) (ls , hs) = (x ∷ ls) , hs
    f (w ⋊ x)  (ls , hs) = ls , ((w , x) ∷ hs)


module _ {V : 𝑆 → Type v} where
  ⊙-assoc : ∀ x y k → x ≡ y ∙ k → V ⊙ x ≡ V ⊙ y ⊙ k
  ⊙-assoc x y k x≡y∙k i z = V ((cong (_∙ z) x≡y∙k ; assoc y k z) i)

  ⊙ε : V ⊙ ε ≡ V
  ⊙ε i x = V (ε∙ x i)

  ⊙-rassoc : ∀ x y → V ⊙ (x ∙ y) ≡ V ⊙ x ⊙ y
  ⊙-rassoc x y i z = V (assoc x y z i)

  merge : Root V → Root V → Root V
  merge (x , xs) (y , ys) with x ≤|≥ y
  ... | inl (k , y≡x∙k) = x , (k ⋊ subst Heap (⊙-assoc y x k y≡x∙k) ys) ∷ xs
  ... | inr (k , x≡y∙k) = y , (k ⋊ subst Heap (⊙-assoc x y k x≡y∙k) xs) ∷ ys

  merges⁺ : Root V → List (Root V) → Root V
  merges⁺ x [] = x
  merges⁺ x₁ (x₂ ∷ []) = merge x₁ x₂
  merges⁺ x₁ (x₂ ∷ x₃ ∷ xs) = merge (merge x₁ x₂) (merges⁺ x₃ xs)

  merges : List (Root V) → Maybe (Root V)
  merges [] = nothing
  merges (x ∷ xs) = just (merges⁺ x xs)

  popMin : Heap V → List (V ε) × Maybe (Root V)
  popMin = map₂ merges ∘ partition

  return : V ε → Heap V
  return x = leaf x ∷ []

  weight : ∃ x × V x → Heap V
  weight (w , x) = (w ⋊ (leaf (subst V (sym (∙ε w)) x) ∷ [])) ∷ []

_>>=_ : Heap V → (∀ {x} → V x → Heap (V ⊙ x)) → Heap V
_>>=_ []             k = []
_>>=_ (leaf x ∷ xs)  k = subst Heap ⊙ε (k x) ++ (xs >>= k)
_>>=_ {V = V} ((w ⋊ x) ∷ xs) k = (w ⋊ (x >>= (subst Heap (⊙-rassoc {V = V} w _) ∘ k))) ∷ (xs >>= k)
