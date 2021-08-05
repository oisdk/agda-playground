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

infixr 5 ⌊_⌋∷_ _⋊_∷_ _++_
infixr 1 _>>=ᴴ_

data Branch (A : Type ℓ) : Type ℓ where
  []    : Branch A
  ⌊_⌋∷_ : A → 𝐹 ε (Branch A) → Branch A
  _⋊_∷_ : (w : 𝑆) → 𝐹 w (Branch A) → 𝐹 ε (Branch A) → Branch A

Heap : Type ℓ → Type ℓ
Heap A = 𝐹 ε (Branch A)

_++_ : 𝐹 w (Branch A) → 𝐹 ε (Branch A) → 𝐹 w (Branch A)
xs ++ ys =
  xs >>=ε λ  {  []        → ys
             ;  (⌊ x  ⌋∷ xs)  → pure (⌊ x  ⌋∷ xs ++ ys)
             ;  (w ⋊ x ∷ xs)  → pure (w ⋊ x ∷ xs ++ ys) }

_>>=ᴴ_ : 𝐹 w (Branch A) → (A → Heap B) → 𝐹 w (Branch B)
xs >>=ᴴ f =
  xs >>=ε λ  {  []              → pure []
             ;  (⌊ x   ⌋∷ xs)  → f x ++ (xs >>=ᴴ f)
             ;  (w ⋊ ys ∷ xs)  → pure (w ⋊ (ys >>=ᴴ f) ∷ (xs >>=ᴴ f)) }

pureᴴ : A → Heap A
pureᴴ x = pure (⌊ x ⌋∷ pure [])

liftᴴ : 𝐹 w A → Heap A
liftᴴ xs = pure (_ ⋊ map (λ x → ⌊ x ⌋∷ pure []) xs ∷ pure [])

Root : Type ℓ → Type ℓ
Root A = ∃[ w ] 𝐹 w (Branch A)

flatten : 𝐹 w (Branch A) → 𝐹 w (List A × List (Root A))
flatten xs =
  xs >>=ε λ  {  []            → pure ([] , [])
             ;  (⌊ x  ⌋∷ xs)  → map (map₁ (x ∷_)) (flatten xs)
             ;  (w ⋊ x ∷ xs)  → map (map₂ ((w , x) ∷_)) (flatten xs) }

module PopMin
  (_≤|≥_ : Total (λ x y → ∃[ z ] (y ≡ x ∙ z)))
  (decomp : ∀ {A B w₁ w₂ w₃} → 𝐹 (w₁ ∙ w₂) A → 𝐹 (w₁ ∙ w₃) B → 𝐹 w₁ (𝐹 w₂ A × 𝐹 w₃ B)) where

  _∪_ : Root A → Root A → Root A
  (wˣ , xs) ∪ (wʸ , ys) with wˣ ≤|≥ wʸ
  ... | inl (k , wʸ≡wˣ∙k) = wˣ , map (λ { (xs , ys) → k ⋊ ys ∷ xs }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) xs) (subst (flip 𝐹 _) wʸ≡wˣ∙k ys))
  ... | inr (k , wˣ≡wʸ∙k) = wʸ , map (λ { (ys , xs) → k ⋊ xs ∷ ys }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) ys) (subst (flip 𝐹 _) wˣ≡wʸ∙k xs))

  ⋃⁺ : Root A → List (Root A) → Root A
  ⋃⁺ x₁ []             = x₁
  ⋃⁺ x₁ (x₂ ∷ [])      = x₁ ∪ x₂
  ⋃⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ∪ x₂) ∪ ⋃⁺ x₃ xs

  ⋃ : List (Root A) → Maybe (Root A)
  ⋃ []       = nothing
  ⋃ (x ∷ xs) = just (⋃⁺ x xs)

  popMin : 𝐹 w (Branch A) → 𝐹 w (List A × Maybe (Root A))
  popMin = map (map₂ ⋃) ∘ flatten
