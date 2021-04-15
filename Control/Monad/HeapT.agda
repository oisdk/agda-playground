{-# OPTIONS --cubical --no-positivity-check --no-termination-check #-}

open import Prelude
open import Algebra
open import Algebra.Monus
open import Relation.Binary

module Control.Monad.HeapT
  {ℓ}
  (gmon : GradedMonad ℓ ℓ ℓ)
  where

open GradedMonad gmon

private
  variable
    w : 𝑆

infixr 5 _∷_
infixr 6 _⋊_
mutual
  Heaped :  Type ℓ → 𝑆 → Type ℓ
  Heaped A w = 𝐹 w (Root A)

  data Root (A : Type ℓ) : Type ℓ where
    []  : Root A
    _∷_ : (x : Branch A) → (xs : 𝐹 ε (Root A)) → Root A

  data Branch (A : Type ℓ) : Type ℓ where
    ⌊_⌋ : A → Branch A
    _⋊_ : (w : 𝑆) (xs : Heaped A w) → Branch A

Heap : Type ℓ → Type ℓ
Heap A = Heaped A ε

infixr 5 _++_
_++_ : 𝐹 w (Root A) → 𝐹 ε (Root A) → 𝐹 w (Root A)
xs ++ ys =
  xs >>=ε λ { []       → ys
            ; (x ∷ xs) → pure (x ∷ xs ++ ys) }

infixr 1 _>>=ᴴ_
_>>=ᴴ_ : Heaped A w → (A → Heap B) → Heaped B w
xs >>=ᴴ f =
  xs >>=ε λ { []            → pure []
            ; (⌊ x ⌋  ∷ xs) → f x ++ (xs >>=ᴴ f)
            ; (w ⋊ ys ∷ xs) → pure (w ⋊ (ys >>=ᴴ f) ∷ (xs >>=ᴴ f)) }

liftT : 𝐹 w A → Heaped A w
liftT = map λ x → ⌊ x ⌋ ∷ pure []

pushT : Heaped A w → Heap A
pushT {w = w} x = pure (w ⋊ x ∷ pure [])

open import Data.List hiding (map)

partition : List (Branch A) → List A × List (Σ 𝑆 (Heaped A))
partition = foldr f ([] , [])
  where
  f : Branch A → List A × List (Σ 𝑆 (Heaped A)) → List A × List (Σ 𝑆 (Heaped A))
  f ⌊ x ⌋    = map₁ (x ∷_)
  f (w ⋊ xs) = map₂ ((w , xs) ∷_)

flattenTop : Heaped A w → 𝐹 w (List (Branch A))
flattenTop xs =
  xs >>=ε λ { []       → pure []
            ; (x ∷ xs) → map (x ∷_) (flattenTop xs) }

module PopMin
  (_≤|≥_ : Total (λ x y → ∃[ z ] (y ≡ x ∙ z)))
  (decomp : ∀ {A B} {w₁ w₂ w₃} → 𝐹 (w₁ ∙ w₂) A → 𝐹 (w₁ ∙ w₃) B → 𝐹 w₁ (𝐹 w₂ A × 𝐹 w₃ B)) where

  _∪_ : ∃ (Heaped A) → ∃ (Heaped A) → ∃ (Heaped A)
  (wˣ , xs) ∪ (wʸ , ys) with wˣ ≤|≥ wʸ
  ... | inl (k , x≤y) = wˣ , map (λ { (xs , ys) → k ⋊ ys ∷ xs }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) xs) (subst (flip 𝐹 _) x≤y ys))
  ... | inr (k , y≤x) = wʸ , map (λ { (ys , xs) → k ⋊ xs ∷ ys }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) ys) (subst (flip 𝐹 _) y≤x xs))

  mergeLists⁺ : ∃ (Heaped A) → List (∃ (Heaped A)) → ∃ (Heaped A)
  mergeLists⁺ x₁ []             = x₁
  mergeLists⁺ x₁ (x₂ ∷ [])      = x₁ ∪ x₂
  mergeLists⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ∪ x₂) ∪ mergeLists⁺ x₃ xs

  mergeLists : List (∃ (Heaped A)) → Maybe (∃ (Heaped A))
  mergeLists []       = nothing
  mergeLists (x ∷ xs) = just (mergeLists⁺ x xs)

  popMin : Heaped A w → 𝐹 w (List A × Maybe (∃ (Heaped A)))
  popMin = map (map₂ mergeLists ∘ partition) ∘ flattenTop
