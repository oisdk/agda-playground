{-# OPTIONS --cubical --safe #-}


open import Algebra
open import Relation.Binary
open import Algebra.Monus

module Data.MonoidalHeap {s} (monus : TMPOM s) where

open TMPOM monus

open import Prelude
open import Data.List using (List; _∷_; [])
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

infixr 6 _∹_&_
data Heap (V : 𝑆 → Type a) : Type (a ℓ⊔ s) where
  [] : Heap V
  _∹_&_ : (key : 𝑆) (val : V key) (children : List (Heap (V ⊙ key))) → Heap V

Heap⋆ : (V : 𝑆 → Type a) → Type (a ℓ⊔ s)
Heap⋆ V = List (Heap V)

private
  variable
    v : Level
    V : 𝑆 → Type v

⊙ε : V ≡ V ⊙ ε
⊙ε {V = V} i x = V (sym (ε∙ x) i)

lemma : ∀ x y k → x ≡ y ∙ k → ⟦ x ⇑⟧ ≡ ⟦ y ⇑⟧ ∘ ⟦ k ⇑⟧
lemma x y k x≡y∙k i z = (cong (_∙ z) x≡y∙k ; assoc y k z) i

merge : Heap V → Heap V → Heap V
merge [] ys = ys
merge (x ∹ xv & xs) [] = x ∹ xv & xs
merge {V = V} (x ∹ xv & xs) (y ∹ yv & ys) with x ≤|≥ y
... | inl (k , x≤y) = x ∹ xv & (k ∹ subst V x≤y yv & subst (List ∘ Heap ∘ _∘_ V) (lemma y x k x≤y) ys ∷ xs)
... | inr (k , x≥y) = y ∹ yv & (k ∹ subst V x≥y xv & subst (List ∘ Heap ∘ _∘_ V) (lemma x y k x≥y) xs ∷ ys)

mergeQs⁺ : Heap V → Heap⋆ V → Heap V
mergeQs⁺ x₁ [] = x₁
mergeQs⁺ x₁ (x₂ ∷ []) = merge x₁ x₂
mergeQs⁺ x₁ (x₂ ∷ x₃ ∷ xs) = merge (merge x₁ x₂) (mergeQs⁺ x₃ xs)

mergeQs : Heap⋆ V → Heap V
mergeQs [] = []
mergeQs (x ∷ xs) = mergeQs⁺ x xs

singleton : ∀ x → V x → Heap V
singleton x xv = x ∹ xv & []

insert : ∀ x → V x → Heap V → Heap V
insert x xv = merge (singleton x xv)

minView : Heap V → Maybe (∃[ p ] × V p × Heap (V ⊙ p))
minView [] = nothing
minView (x ∹ xv & xs) = just (x , xv , mergeQs xs)

variable
  v₁ v₂ : Level
  V₁ : 𝑆 → Type v₁
  V₂ : 𝑆 → Type v₂

mutual
  maps : (∀ {x} → V₁ x → V₂ x) → Heap⋆ V₁ → Heap⋆ V₂
  maps f [] = []
  maps f (x ∷ xs) = map f x ∷ maps f xs

  map : (∀ {x} → V₁ x → V₂ x) → Heap V₁ → Heap V₂
  map f [] = []
  map f (k ∹ v & xs) = k ∹ f v & maps f xs

mutual
  size : Heap V → ℕ
  size [] = zero
  size (_ ∹ _ & xs) = suc (sizes xs)

  sizes : Heap⋆ V → ℕ
  sizes [] = 0
  sizes (x ∷ xs) = size x ℕ.+ sizes xs

open import Data.Maybe using (maybe)
open import Path.Reasoning
open import Cubical.Foundations.Prelude using (substRefl)

lemma₂ : ∀ {x y : 𝑆 → 𝑆} xs (p : x ≡ y) → sizes (subst (List ∘ Heap ∘ _∘_ V) p xs) ≡ sizes xs
lemma₂ {V = V} xs = J (λ _ p → sizes (subst (List ∘ Heap ∘ _∘_ V) p xs) ≡ sizes xs) (cong sizes (substRefl {B = List ∘ Heap ∘ _∘_ V} xs))

merge-size : (xs ys : Heap V) → size (merge xs ys) ≡ size xs ℕ.+ size ys
merge-size [] ys = refl
merge-size (x ∹ xv & xs) [] = sym (ℕ.+-idʳ _)
merge-size {V = V} (x ∹ xv & xs) (y ∹ yv & ys) with x ≤|≥ y
merge-size {V = V} (x ∹ xv & xs) (y ∹ yv & ys) | inr (k , x≥y) =
  suc (suc (sizes (subst (List ∘ Heap ∘ _∘_ V) (lemma x y k x≥y) xs)) ℕ.+ sizes ys) ≡˘⟨ ℕ.+-suc _ (sizes ys) ⟩
  suc (sizes (subst (List ∘ Heap ∘ _∘_ V) (lemma x y k x≥y) xs)) ℕ.+ suc (sizes ys) ≡⟨ cong (ℕ._+ suc (sizes ys)) (cong suc (lemma₂ {V = V} xs (lemma x y k x≥y))) ⟩
  suc (sizes xs) ℕ.+ suc (sizes ys) ∎
merge-size {V = V} (x ∹ xv & xs) (y ∹ yv & ys) | inl (k , x≤y) =
  suc (suc (sizes (subst (List ∘ Heap ∘ _∘_ V) (lemma y x k x≤y) ys)) ℕ.+ sizes xs) ≡˘⟨ ℕ.+-suc _ (sizes xs) ⟩
  suc (sizes (subst (List ∘ Heap ∘ _∘_ V) (lemma y x k x≤y) ys)) ℕ.+ suc (sizes xs) ≡⟨ cong (ℕ._+ suc (sizes xs)) (cong suc (lemma₂ {V = V} ys (lemma y x k x≤y))) ⟩
  suc (sizes ys) ℕ.+ suc (sizes xs) ≡⟨ ℕ.+-comm (suc (sizes ys)) (suc (sizes xs)) ⟩
  suc (sizes xs) ℕ.+ suc (sizes ys) ∎

mutual
  minViewSizes : (xs : Heap⋆ V) → sizes xs ≡ size (mergeQs xs)
  minViewSizes [] = refl
  minViewSizes (x ∷ xs) = minViewSizes⁺ x xs

  minViewSizes⁺ : (x : Heap V) → (xs : Heap⋆ V) → sizes (x ∷ xs) ≡ size (mergeQs⁺ x xs)
  minViewSizes⁺ x₁ [] = ℕ.+-idʳ _
  minViewSizes⁺ x₁ (x₂ ∷ []) = cong (λ z → size x₁ ℕ.+ z) (ℕ.+-idʳ _) ; sym (merge-size x₁ x₂)
  minViewSizes⁺ x₁ (x₂ ∷ x₃ ∷ xs) =
    size x₁ ℕ.+ (size x₂ ℕ.+ sizes (x₃ ∷ xs)) ≡˘⟨ ℕ.+-assoc (size x₁) (size x₂) (sizes (x₃ ∷ xs)) ⟩
    (size x₁ ℕ.+ size x₂) ℕ.+ sizes (x₃ ∷ xs) ≡⟨ cong ((size x₁ ℕ.+ size x₂) ℕ.+_) (minViewSizes⁺ x₃ xs) ⟩
    (size x₁ ℕ.+ size x₂) ℕ.+ size (mergeQs⁺ x₃ xs) ≡˘⟨ cong (ℕ._+ size (mergeQs⁺ x₃ xs)) (merge-size x₁ x₂) ⟩
    size (merge x₁ x₂) ℕ.+ size (mergeQs⁺ x₃ xs) ≡˘⟨ merge-size (merge x₁ x₂) (mergeQs⁺ x₃ xs) ⟩
    size (merge (merge x₁ x₂) (mergeQs⁺ x₃ xs)) ∎

minViewSize : (xs : Heap V) → size xs ≡ maybe zero (suc ∘ size ∘ snd ∘ snd) (minView xs)
minViewSize [] = refl
minViewSize (x ∹ xv & xs) = cong suc (minViewSizes xs)

zer : Heap⋆ V
zer = []

one : Heap⋆ V
one = [] ∷ []

open import Data.List using (_++_; concatMap)

_<+>_ : Heap⋆ V → Heap⋆ V → Heap⋆ V
_<+>_ = _++_

multIn : (p : 𝑆 → 𝑆) → (c : ∀ {x y} → V (p x) → V y → V (p (x ∙ y))) → (V ⇒ V ∘ p) → Heap⋆ (V ∘ p) → Heap⋆ V → Heap⋆ (V ∘ p)
multIn {V = V} p c f [] ys = []
multIn {V = V} p c f ([] ∷ xs) ys = maps f ys ++ multIn p c f xs ys
multIn {V = V} p c f (x ∹ xv & xc ∷ xs) ys = x ∹ xv & multIn (p ∘ ⟦ x ⇑⟧) (λ v₁ v₂ → subst V (cong p (assoc x _ _)) (c v₁ v₂)) (c xv) xc ys ∷ multIn p c f xs ys

appl : (∀ {x y} → V x → V y → V (x ∙ y)) → Heap⋆ V → Heap⋆ V → Heap⋆ V
appl {V = V} f xs ys = multIn {V = V} id f id xs ys
