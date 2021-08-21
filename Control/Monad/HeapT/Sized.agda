{-# OPTIONS --cubical --no-positivity-check --no-termination-check --allow-unsolved-metas #-}

open import Prelude
open import Algebra
open import Algebra.Monus
open import Relation.Binary
open import Data.Maybe
open import Data.List using (List; _∷_; []; foldr)

module Control.Monad.HeapT.Sized
  {ℓ}
  (mon : CTMAPOM ℓ)
  (gmon : GradedMonad (CTMAPOM.monoid mon) ℓ ℓ)
  where

open CTMAPOM mon
open GradedMonad gmon

private
  variable
    w i j : 𝑆

infixr 5 _∷_
infixr 6 _⋊_

mutual
  data Root′ (A : Type ℓ) (i : 𝑆) : Type ℓ where
    _⋊_ : ∀ w → (w < i → 𝐹 w (Branch A (i ∸ w))) → Root′ A i

  data Node (A : Type ℓ) (i : 𝑆) : Type ℓ where
    ⌊_⌋ : A → Node A i
    ⌈_⌉ : Root′ A i → Node A i

  data Branch (A : Type ℓ) (i : 𝑆) : Type ℓ where
    []  : Branch A i
    _∷_ : Node A i → 𝐹 ε (Branch A i) → Branch A i

Heap : Type ℓ → Type ℓ
Heap A = ∀ {i} → 𝐹 ε (Branch A i)

infixr 5 _++_
_++_ : 𝐹 w (Branch A i) → 𝐹 ε (Branch A i) → 𝐹 w (Branch A i)
xs ++ ys =
  xs >>=ε λ  {  []       → ys
             ;  (x ∷ xs) → pure (x ∷ xs ++ ys) }

infixr 1 _>>=ᴺ_ _>>=ᴴ_
mutual
  _>>=ᴺ_ : Node A i → (A → Heap B) → 𝐹 ε (Branch B i)
  ⌊ x ⌋  >>=ᴺ f = f x
  ⌈ w ⋊ s ⌉  >>=ᴺ f = pure (⌈ w ⋊ (λ w<i → s w<i >>=ᴴ f) ⌉ ∷ pure [])

  _>>=ᴴ_ : 𝐹 w (Branch A i) → (A → Heap B) → 𝐹 w (Branch B i)
  xs >>=ᴴ f =
    xs >>=ε λ  {  []        → pure []
               ;  (x ∷ xs)  → (x >>=ᴺ f) ++ (xs >>=ᴴ f) }

pureᴴ : A → Heap A
pureᴴ x = pure (⌊ x ⌋ ∷ pure [])

liftᴴ : 𝐹 w A → Heap A
liftᴴ xs = pure (⌈ _ ⋊ const (map (λ x → ⌊ x ⌋ ∷ pure []) xs) ⌉ ∷ pure [])

flatten : 𝐹 w (Branch A i) → 𝐹 w (List A × List (Root′ A i))
flatten xs =
  xs >>=ε λ  {  []            → pure ([] , [])
             ;  (⌊ x ⌋ ∷ xs)  → map (map₁ (x ∷_)) (flatten xs)
             ;  (⌈ x ⌉ ∷ xs)  → map (map₂ (x ∷_)) (flatten xs) }

module PopMin
  (decomp : ∀ {A B w₁ w₂ w₃} → 𝐹 (w₁ ∙ w₂) A → 𝐹 (w₁ ∙ w₃) B → 𝐹 w₁ (𝐹 w₂ A × 𝐹 w₃ B))
  (strong : {w : 𝑆} → {A B : Type ℓ} → (A → 𝐹 w B) → 𝐹 w (A → B))
  where

  _∪_ : Root′ A i → Root′ A i → Root′ A i
  _∪_ {i = i} (wˣ ⋊ xs) (wʸ ⋊ ys) with wˣ ≤|≥ wʸ
  ... | inr (k , wˣ≡wʸ∙k) = {!!}
  ... | inl (k , wʸ≡wˣ∙k) = wˣ ⋊ λ wˣ<i → map (λ { (xs , ys) → ⌈ k ⋊ (λ k<i∸wˣ → subst (𝐹 _ ∘ Branch _) (cong (_ ∸_) wʸ≡wˣ∙k ; sym (∸‿assoc _ wˣ k)) (map (_$ subst (_< i) (sym wʸ≡wˣ∙k) {!!})  ys)) ⌉ ∷ xs }) (decomp (subst (flip 𝐹 _) (sym (∙ε _)) (xs wˣ<i)) (subst (flip 𝐹 _) wʸ≡wˣ∙k (strong ys)))
    where
    lemma : ∀ x y z → x < z → y < z ∸ x → x ∙ y < z
    lemma = {!!}

  -- ⋃⁺ : Root A → List (Root A) → Root A
  -- ⋃⁺ x₁ []             = x₁
  -- ⋃⁺ x₁ (x₂ ∷ [])      = x₁ ∪ x₂
  -- ⋃⁺ x₁ (x₂ ∷ x₃ ∷ xs) = (x₁ ∪ x₂) ∪ ⋃⁺ x₃ xs

  -- ⋃ : List (Root A) → Maybe (Root A)
  -- ⋃ []       = nothing
  -- ⋃ (x ∷ xs) = just (⋃⁺ x xs)

  -- popMin : 𝐹 w (Branch A) → 𝐹 w (List A × Maybe (Root A))
  -- popMin = map (map₂ ⋃) ∘ flatten
