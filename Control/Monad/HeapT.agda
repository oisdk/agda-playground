{-# OPTIONS --cubical --no-positivity-check --no-termination-check #-}

open import Prelude
open import Algebra
open import Algebra.Monus
open import Relation.Binary
open import Data.Maybe
open import Data.List using (List; _∷_; []; foldr)

module Control.Monad.HeapT
  {ℓ}
  (monoid : Monoid ℓ)
  (gmon : GradedMonad monoid ℓ ℓ)
  where

open Monoid monoid
open GradedMonad gmon

private
  variable
    w : 𝑆

infixr 5 _∷_
infixr 6 _⋊_

mutual
  record Root (A : Type ℓ) : Type ℓ where
    coinductive
    constructor _⋊_
    field
      weight : 𝑆
      step : 𝐹 weight (Branch A)

  data Node (A : Type ℓ) : Type ℓ where
    ⌊_⌋ : A → Node A
    ⌈_⌉ : Root A → Node A

  data Branch (A : Type ℓ) : Type ℓ where
    []  : Branch A
    _∷_ : Node A → 𝐹 ε (Branch A) → Branch A
open Root public

Heap : Type ℓ → Type ℓ
Heap A = 𝐹 ε (Branch A)

infixr 5 _++_
_++_ : 𝐹 w (Branch A) → 𝐹 ε (Branch A) → 𝐹 w (Branch A)
xs ++ ys =
  xs >>=ε λ  {  []       → ys
             ;  (x ∷ xs) → pure (x ∷ xs ++ ys) }

infixr 1 _>>=ᴺ_ _>>=ᴴ_
mutual
  _>>=ᴺ_ : Node A → (A → Heap B) → Heap B
  ⌊ x ⌋  >>=ᴺ f = f x
  ⌈ x ⌉  >>=ᴺ f = pure (⌈ weight x ⋊ (step x >>=ᴴ f) ⌉ ∷ pure [])

  _>>=ᴴ_ : 𝐹 w (Branch A) → (A → Heap B) → 𝐹 w (Branch B)
  xs >>=ᴴ f =
    xs >>=ε λ  {  []        → pure []
               ;  (x ∷ xs)  → (x >>=ᴺ f) ++ (xs >>=ᴴ f) }

pureᴴ : A → Heap A
pureᴴ x = pure (⌊ x ⌋ ∷ pure [])

liftᴴ : 𝐹 w A → Heap A
liftᴴ xs = pure (⌈ _ ⋊ map (λ x → ⌊ x ⌋ ∷ pure []) xs ⌉ ∷ pure [])

flatten : 𝐹 w (Branch A) → 𝐹 w (List A × List (Root A))
flatten xs =
  xs >>=ε λ  {  []            → pure ([] , [])
             ;  (⌊ x ⌋ ∷ xs)  → map (map₁ (x ∷_)) (flatten xs)
             ;  (⌈ x ⌉ ∷ xs)  → map (map₂ (x ∷_)) (flatten xs) }

module PopMin
  (_≤|≥_ : Total (λ x y → ∃[ z ] (y ≡ x ∙ z)))
  (decomp : ∀ {A B w₁ w₂ w₃} → 𝐹 (w₁ ∙ w₂) A → 𝐹 (w₁ ∙ w₃) B → 𝐹 w₁ (𝐹 w₂ A × 𝐹 w₃ B)) where

  _∪_ : Root A → Root A → Root A
  xs ∪ ys with weight xs ≤|≥ weight ys
  ... | inl (k , wʸ≡wˣ∙k) = weight xs ⋊ map (λ { (xs , ys) → ⌈ k ⋊ ys ⌉ ∷ xs }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) (step xs)) (subst (flip 𝐹 _) wʸ≡wˣ∙k (step ys)))
  ... | inr (k , wˣ≡wʸ∙k) = weight ys ⋊ map (λ { (ys , xs) → ⌈ k ⋊ xs ⌉ ∷ ys }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) (step ys)) (subst (flip 𝐹 _) wˣ≡wʸ∙k (step xs)))

  ⋃⁺ : Root A → List (Root A) → Root A
  ⋃⁺ x₁ []             = x₁
  ⋃⁺ x₁ (x₂ ∷ [])      = x₁ ∪ x₂
  ⋃⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ∪ x₂) ∪ ⋃⁺ x₃ xs

  ⋃ : List (Root A) → Maybe (Root A)
  ⋃ []       = nothing
  ⋃ (x ∷ xs) = just (⋃⁺ x xs)

  popMin : 𝐹 w (Branch A) → 𝐹 w (List A × Maybe (Root A))
  popMin = map (map₂ ⋃) ∘ flatten
