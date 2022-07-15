{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra
open import Algebra.Monus
open import Prelude
open import Relation.Binary

module Algebra.Monus.Heap (mon : TMAPOM ℓzero) (≺-wf : WellFounded (TMAPOM._≺_ mon)) where

open TMAPOM mon

-- open TotalOrder totalOrder hiding (_<ᵇ_)

min-max : 𝑆 → 𝑆 → 𝑆 × 𝑆
min-max x y = either′ (const (y , x)) (const (x , y)) (x ≤|≥ y)

_⊔_ : 𝑆 → 𝑆 → 𝑆
x ⊔ y = snd (min-max x y)

_⊓_ : 𝑆 → 𝑆 → 𝑆
x ⊓ y = fst (min-max x y)

infixr 5 _∷_
data ⟅_⟆ (A : Type a) : Type a where
  ⟅⟆  : ⟅ A ⟆
  _∷_ : 𝑆 × A → ⟅ A ⟆ → ⟅ A ⟆

  com : ∀ w₁ x w₂ y xs → (w₁ , x) ∷ (w₂ , y) ∷ xs ≡ (w₂ , y) ∷ (w₁ , x) ∷ xs
  dup : ∀ w₁ w₂ x xs → (w₁ , x) ∷ (w₂ , x) ∷ xs ≡ (w₁ ⊓ w₂ , x) ∷ xs

  trunc : isSet ⟅ A ⟆

module _ (P : ⟅ A ⟆ → Type b)
         (f : (w : 𝑆) → (x : A) → (xs : ⟅ A ⟆) → P xs → P ((w , x) ∷ xs))
         (n : P ⟅⟆)
         (nset : ∀ xs → isSet (P xs))
         (fcom : ∀ w₁ x w₂ y xs → (Pxs : P xs) → PathP (λ i → P (com w₁ x w₂ y xs i)) (f w₁ x _ (f w₂ y xs Pxs)) (f w₂ y _ (f w₁ x xs Pxs)))
         (fdup : ∀ w₁ w₂ x xs Pxs → PathP (λ i → P (dup w₁ w₂ x xs i)) (f w₁ x _ (f w₂ x xs Pxs)) (f (w₁ ⊓ w₂) x xs Pxs))
         where
  elim-weight : ∀ xs → P xs
  elim-weight ⟅⟆ = n
  elim-weight ((w , x) ∷ xs) = f w x xs (elim-weight xs)
  elim-weight (com w₁ x w₂ y xs i) = fcom w₁ x w₂ y xs (elim-weight xs) i
  elim-weight (dup w₁ w₂ x xs i) = fdup w₁ w₂ x xs (elim-weight xs) i
  elim-weight (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2
      nset
      (elim-weight xs) (elim-weight ys)
      (cong elim-weight p) (cong elim-weight q)
      (trunc xs ys p q)
      i j

module _ (f : 𝑆 → A → B → B)
         (n : B)
         (nset : isSet B)
         (fcom : ∀ w₁ x w₂ y Pxs → f w₁ x (f w₂ y Pxs) ≡ f w₂ y (f w₁ x Pxs))
         (fdup : ∀ w₁ w₂ x Pxs → f w₁ x (f w₂ x Pxs) ≡ f (w₁ ⊓ w₂) x Pxs)
         where
  rec-weight : ⟅ A ⟆ → B
  rec-weight =
    elim-weight
      (λ _ → B)
      (λ w x _ → f w x)
      n
      (λ _ → nset)
      (λ w₁ x w₂ y _ → fcom w₁ x w₂ y)
      (λ w₁ w₂ x _ → fdup w₁ w₂ x)

_∪_ : ⟅ A ⟆ → ⟅ A ⟆ → ⟅ A ⟆
xs ∪ ys = rec-weight (λ w x xs → (w , x) ∷ xs) ys trunc com dup xs

⊓-distrib : ∀ x y z → x ∙ (y ⊓ z) ≡ (x ∙ y) ⊓ (x ∙ z)
⊓-distrib x y z with y ≤|≥ z | (x ∙ y) ≤|≥ (x ∙ z)
... | inl y≤z | inl x∙y≤x∙z = refl
... | inr y≥z | inl x∙y≤x∙z = antisym x∙y≤x∙z (≤-cong x y≥z)
... | inl y≤z | inr x∙y≥x∙z = antisym x∙y≥x∙z (≤-cong x y≤z)
... | inr y≥z | inr x∙y≥x∙z = refl


cond : 𝑆 → ⟅ A ⟆ → ⟅ A ⟆
cond w =
  rec-weight
    (λ w′ x xs → (w ∙ w′ , x) ∷ xs)
    ⟅⟆
    trunc
    (λ w₁ x w₂ → com (w ∙ w₁) x (w ∙ w₂))
    λ w₁ w₂ x Pxs → dup (w ∙ w₁) (w ∙ w₂) x Pxs ; cong (λ w′ → (w′ , x) ∷ Pxs) (sym (⊓-distrib w w₁ w₂))  

-- _>>=_ : ⟅ A ⟆ → (A → ⟅ B ⟆) → ⟅ B ⟆
-- xs >>= k = rec-weight (λ w x xs → (cond w (k x)) ∪ xs) ⟅⟆ trunc {!!} {!!} xs

-- map : (A → B) → ⟅ A ⟆ → ⟅ B ⟆
-- map f = rec-weight (λ w x xs → (w , f x) ∷ xs) ⟅⟆ trunc {!!} {!!}

open import Data.List

mutual
  record Root (A : Type a) : Type a where
    coinductive; constructor ⟪_⟫
    field tree : List (Branch A)

  data Branch (A : Type a) : Type a where
    leaf : A → Branch A
    _[_]⋊_ : ∀ w → w ≢ ε → Root A → Branch A
open Root

Heap′ : Type a → Type a
Heap′ A = List (Branch A)

inf : ∀ w → w ≢ ε → Root A
inf w w≢ε .tree = (w [ w≢ε ]⋊ inf w w≢ε) ∷ []

mutual
  restrict″ : ∀ w → Acc _≺_ w → Branch A → ⟅ A ⟆ → ⟅ A ⟆
  restrict″ w wf (leaf x) xs = (ε , x) ∷ xs
  restrict″ w wf (x [ x≢ε ]⋊ xc) xs with x ≤? w
  restrict″ w wf (x [ x≢ε ]⋊ xc) xs | no  x≮w = xs
  restrict″ w (acc wf) (x [ x≢ε ]⋊ xc) xs | yes (k , x≤w) =
    cond x (restrict′ k (wf _ (x , x≤w ; comm _ _ , x≢ε)) (xc .tree)) ∪ xs

  restrict′ : ∀ w → Acc _≺_ w → Heap′ A → ⟅ A ⟆
  restrict′ w a = foldr (restrict″ w a) ⟅⟆

restrict : 𝑆 → Heap′ A → ⟅ A ⟆
restrict w = restrict′ w (≺-wf w)

open import HITs.SetQuotients

UpTo : Heap′ A → Heap′ A → Type _
UpTo xs ys = ∀ w → restrict w xs ≡ restrict w ys

Heap : Type a → Type a
Heap A = Heap′ A / UpTo

open import Cubical.HITs.SetQuotients using (rec2)

++-lhs : (xs ys zs : Heap′ A) → UpTo xs ys → UpTo (xs ++ zs) (ys ++ zs)
++-lhs xs ys zs r w = let p = r w in {!!}

++-rhs : (xs ys zs : Heap′ A) → UpTo ys zs → UpTo (xs ++ ys) (xs ++ zs)
++-rhs xs ys zs r w = let p = r w in {!!}

_++H_ : Heap A → Heap A → Heap A
_++H_ = rec2 squash/ (λ xs ys → [ xs ++ ys ]) (λ xs ys zs r → eq/ _ _ (++-lhs xs ys zs r)) λ xs ys zs r → eq/ _ _ (++-rhs xs ys zs r)

-- -- Heap′ : Type a → Type a
-- -- Heap′ A = List (A ×)




-- data Heap (A : Type a) : Type a where
--   [_]    : ⟅ Tree A (Heap A) ⟆ → Heap A
--   flat/  : (xs : ⟅ Tree A ⟅ Tree A (Heap A) ⟆ ⟆)
--          → [ (do x ← xs ; (ε , root x ◁ [ ⟅⟆ ]) ∷ rest x) ] ≡ [ map (map-rest [_]) xs ]
    
  
