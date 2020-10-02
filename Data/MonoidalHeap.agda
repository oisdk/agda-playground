{-# OPTIONS --cubical --safe #-}


open import Algebra
open import Relation.Binary
import Algebra.Construct.OrderedMonoid as OrdMon

module Data.MonoidalHeap {s} (mon : Monoid s) (_≤?_ : Total (OrdMon._≤_ mon)) where

open Monoid mon
open OrdMon mon

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
record Heap⁺ {v} (V : 𝑆 → Type v) : Type (v ℓ⊔ s) where
  constructor _∹_&_
  inductive
  field
    key : 𝑆
    val : V key
    children : List (Heap⁺ (V ⊙ key))
open Heap⁺ public

data Heap (V : 𝑆 → Type a) : Type (a ℓ⊔ s) where
  leaf : Heap V
  node : Heap⁺ V → Heap V

private
  variable
    v : Level
    V : 𝑆 → Type v

lemma : ∀ x y k → x ≡ y ∙ k → ⟦ x ⇑⟧ ≡ ⟦ y ⇑⟧ ∘ ⟦ k ⇑⟧
lemma x y k x≡y∙k i z = (cong (_∙ z) x≡y∙k ; assoc y k z) i

merge⁺ : Heap⁺ V → Heap⁺ V → Heap⁺ V
merge⁺ {V = V} (x ∹ xv & xs) (y ∹ yv & ys) with x ≤? y
... | inl (k , x≤y) = x ∹ xv & (k ∹ subst V x≤y yv & subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma y x k x≤y) ys ∷ xs)
... | inr (k , x≥y) = y ∹ yv & (k ∹ subst V x≥y xv & subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma x y k x≥y) xs ∷ ys)

merge : Heap V → Heap V → Heap V
merge leaf ys = ys
merge (node xs) leaf = node xs
merge (node xs) (node ys) = node (merge⁺ xs ys)

mergeQs⁺ : Heap⁺ V → List (Heap⁺ V) → Heap⁺ V
mergeQs⁺ x₁ [] = x₁
mergeQs⁺ x₁ (x₂ ∷ []) = merge⁺ x₁ x₂
mergeQs⁺ x₁ (x₂ ∷ x₃ ∷ xs) = merge⁺ (merge⁺ x₁ x₂) (mergeQs⁺ x₃ xs)

mergeQs : List (Heap⁺ V) → Heap V
mergeQs [] = leaf
mergeQs (x ∷ xs) = node (mergeQs⁺ x xs)

singleton⁺ : ∀ x → V x → Heap⁺ V
singleton⁺ x xv .key = x
singleton⁺ x xv .val = xv
singleton⁺ x xv .children = []

singleton : ∀ x → V x → Heap V
singleton x xv = node (singleton⁺ x xv)

insert⁺ : ∀ x → V x → Heap⁺ V → Heap⁺ V
insert⁺ x xv = merge⁺ (singleton⁺ x xv)

insert : ∀ x → V x → Heap V → Heap V
insert x xv leaf = singleton x xv
insert x xv (node xs) = node (insert⁺ x xv xs)

minView : Heap V → Maybe (∃[ p ] V p × Heap (V ⊙ p))
minView leaf = nothing
minView (node (x ∹ xv & xs)) = just (x , xv , mergeQs xs)

variable
  v₁ v₂ : Level
  V₁ : 𝑆 → Type v₁
  V₂ : 𝑆 → Type v₂

mutual
  maps⁺ : (∀ {x} → V₁ x → V₂ x) → List (Heap⁺ V₁) → List (Heap⁺ V₂)
  maps⁺ f [] = []
  maps⁺ f (x ∷ xs) = map⁺ f x ∷ maps⁺ f xs

  map⁺ : (∀ {x} → V₁ x → V₂ x) → Heap⁺ V₁ → Heap⁺ V₂
  map⁺ f (k ∹ v & xs) = k ∹ f v & maps⁺ f xs

map : (∀ {x} → V₁ x → V₂ x) → Heap V₁ → Heap V₂
map f leaf = leaf
map f (node x) = node (map⁺ f x)

mutual
  size⁺ : Heap⁺ V → ℕ
  size⁺ xs = suc (sizes⁺ (xs .children))

  sizes⁺ : List (Heap⁺ V) → ℕ
  sizes⁺ [] = 0
  sizes⁺ (x ∷ xs) = size⁺ x ℕ.+ sizes⁺ xs

size : Heap V → ℕ
size leaf = 0
size (node x) = size⁺ x

open import Data.Maybe using (maybe)
open import Path.Reasoning
open import Cubical.Foundations.Prelude using (substRefl)

lemma₂ : ∀ {x y : 𝑆 → 𝑆} xs (p : x ≡ y) → sizes⁺ (subst (List ∘ Heap⁺ ∘ _∘_ V) p xs) ≡ sizes⁺ xs
lemma₂ {V = V} xs = J (λ _ p → sizes⁺ (subst (List ∘ Heap⁺ ∘ _∘_ V) p xs) ≡ sizes⁺ xs) (cong sizes⁺ (substRefl {B = List ∘ Heap⁺ ∘ _∘_ V} xs))

merge⁺-size : (xs ys : Heap⁺ V) → size⁺ (merge⁺ xs ys) ≡ size⁺ xs ℕ.+ size⁺ ys
merge⁺-size {V = V} (x ∹ xv & xs) (y ∹ yv & ys) with x ≤? y
merge⁺-size {V = V} (x ∹ xv & xs) (y ∹ yv & ys) | inr (k , x≥y) =
  suc (suc (sizes⁺ (subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma x y k x≥y) xs)) ℕ.+ sizes⁺ ys) ≡˘⟨ ℕ.+-suc _ (sizes⁺ ys) ⟩
  suc (sizes⁺ (subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma x y k x≥y) xs)) ℕ.+ suc (sizes⁺ ys) ≡⟨ cong (ℕ._+ suc (sizes⁺ ys)) (cong suc (lemma₂ {V = V} xs (lemma x y k x≥y))) ⟩
  suc (sizes⁺ xs) ℕ.+ suc (sizes⁺ ys) ∎
merge⁺-size {V = V} (x ∹ xv & xs) (y ∹ yv & ys) | inl (k , x≤y) =
  suc (suc (sizes⁺ (subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma y x k x≤y) ys)) ℕ.+ sizes⁺ xs) ≡˘⟨ ℕ.+-suc _ (sizes⁺ xs) ⟩
  suc (sizes⁺ (subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma y x k x≤y) ys)) ℕ.+ suc (sizes⁺ xs) ≡⟨ cong (ℕ._+ suc (sizes⁺ xs)) (cong suc (lemma₂ {V = V} ys (lemma y x k x≤y))) ⟩
  suc (sizes⁺ ys) ℕ.+ suc (sizes⁺ xs) ≡⟨ ℕ.+-comm (suc (sizes⁺ ys)) (suc (sizes⁺ xs)) ⟩
  suc (sizes⁺ xs) ℕ.+ suc (sizes⁺ ys) ∎


mutual
  minViewSize⁺ : (xs : Heap⁺ V) → size⁺ xs ≡ suc (size (mergeQs (xs .children)))
  minViewSize⁺ xs = cong suc (minViewSizes⁺ (xs .children))

  minViewSizes⁺ : (xs : List (Heap⁺ V)) → sizes⁺ xs ≡ size (mergeQs xs)
  minViewSizes⁺ [] = refl
  minViewSizes⁺ (x ∷ xs) = minViewSizes⁺⁺ x xs

  minViewSizes⁺⁺ : (x : Heap⁺ V) → (xs : List (Heap⁺ V)) → sizes⁺ (x ∷ xs) ≡ size⁺ (mergeQs⁺ x xs)
  minViewSizes⁺⁺ x₁ [] = cong suc (ℕ.+-idʳ _)
  minViewSizes⁺⁺ x₁ (x₂ ∷ []) = cong (λ z → size⁺ x₁ ℕ.+ z) (ℕ.+-idʳ _) ; sym (merge⁺-size x₁ x₂)
  minViewSizes⁺⁺ x₁ (x₂ ∷ x₃ ∷ xs) =
    size⁺ x₁ ℕ.+ (size⁺ x₂ ℕ.+ sizes⁺ (x₃ ∷ xs)) ≡˘⟨ ℕ.+-assoc (size⁺ x₁) (size⁺ x₂) (sizes⁺ (x₃ ∷ xs)) ⟩
    (size⁺ x₁ ℕ.+ size⁺ x₂) ℕ.+ sizes⁺ (x₃ ∷ xs) ≡⟨ cong ((size⁺ x₁ ℕ.+ size⁺ x₂) ℕ.+_) (minViewSizes⁺⁺ x₃ xs) ⟩
    (size⁺ x₁ ℕ.+ size⁺ x₂) ℕ.+ size⁺ (mergeQs⁺ x₃ xs) ≡˘⟨ cong (ℕ._+ size⁺ (mergeQs⁺ x₃ xs)) (merge⁺-size x₁ x₂) ⟩
    size⁺ (merge⁺ x₁ x₂) ℕ.+ size⁺ (mergeQs⁺ x₃ xs) ≡˘⟨ merge⁺-size (merge⁺ x₁ x₂) (mergeQs⁺ x₃ xs) ⟩
    size⁺ (merge⁺ (merge⁺ x₁ x₂) (mergeQs⁺ x₃ xs)) ∎

minViewSize : (xs : Heap V) → size xs ≡ maybe zero (suc ∘ size ∘ snd ∘ snd) (minView xs)
minViewSize leaf = refl
minViewSize (node x) = minViewSize⁺ x

-- open import Data.Nat.Order

-- toList : (xs : Heap V) → List (∃[ p ] V p)
-- toList xs = go (size xs) xs (≡ⁿ-refl (size xs))
--   where
--   go : (n : ℕ) → (xs : Heap V) → (n ≡ⁿ size xs) → List (∃[ p ] V p)
--   go n xs p with minView xs
--   go n xs p | nothing = []
--   go n xs p | just x = {!x!}

-- _>>=⁺_ : Heap⁺ V₁ → (∀ {k} → V₁ k → Heap (V₂ ∘ _∙_ k)) → Heap V₂
-- xs >>=⁺ f = {!!}

-- _>>=_ : Heap V₁ → (∀ {k} → V₁ k → Heap (V₂ ∘ _∙_ k)) → Heap V₂
-- leaf >>= f = leaf
-- node x >>= f = x >>=⁺ f
