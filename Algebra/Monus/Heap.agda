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
  Forest : Type a → Type a
  Forest A = List (Branch A)

  Branch : Type a → Type a
  Branch A = A ⊎ Root A

  Root : Type a → Type a
  Root A = Σ[ w ⦂ 𝑆 ] × Step A w

  record Deep (A : Type a) (w : 𝑆) : Type a where
    coinductive; constructor deep
    field
      depth : w ≢ ε
      force : Forest A

  data Step (A : Type a) (w : 𝑆) : Type a where
    fin : Forest A → Step A w
    inf : Deep A w → Step A w

open Deep public

rinf : ∀ w → w ≢ ε → Forest A
rinf w w≢ε = inr (w , inf λ where .depth → w≢ε ; .force → rinf w w≢ε) ∷ []

map-forest : ∀ {w} → (Forest A → Forest B) → Deep A w → Deep B w
map-forest f xs .depth = xs .depth
map-forest f xs .force = f (xs .force)

un-step : ∀ {w₁ w₂} → Step A w₁ → Step A w₂
un-step (fin x) = fin x
un-step (inf x) = fin (x .force)

_◃_ : ∀ {w} → Root A → Step A w → Step A w
x ◃ fin xs = fin (inr x ∷ xs)
x ◃ inf xs = inf (map-forest (inr x ∷_) xs)

_⋈_ : Root A → Root A → Root A
(xʷ , xs) ⋈ (yʷ , ys) with xʷ ≤|≥ yʷ 
... | inl (k , x≤y) = xʷ , ((k , un-step ys) ◃ xs)
... | inr (k , y≤x) = yʷ , ((k , un-step xs) ◃ ys)

mutual
  restrict‴ : 𝑆 → ∀ w → Acc _≺_ w → ∀ w′ → w′ ≤ w → w′ ≢ ε → Forest A → ⟅ A ⟆ → ⟅ A ⟆
  restrict‴ aw w (acc wf) w′ (k , w′≤w) w′≢ε =
    restrict′ (w′ ∙ aw) k (wf k (w′ , w′≤w ; comm _ _ , w′≢ε))

  restrict″ : 𝑆 → ∀ w → Acc _≺_ w → Branch A → ⟅ A ⟆ → ⟅ A ⟆
  restrict″ aw w wf (inl x) xs = (aw , x) ∷ xs
  restrict″ aw w wf (inr (w′ , x)) xs with w′ ≤? w
  restrict″ aw w wf (inr (w′ , x)) xs | no  w′≰w = xs
  restrict″ aw w wf (inr (w′ , inf x)) xs | yes w′≤w = restrict‴ aw w wf w′ w′≤w (x .depth) (x .force) xs
  restrict″ aw w wf (inr (w′ , fin x)) xs | yes w′≤w with w′ ≟ ε 
  ... | yes w′≡ε = restrict′ aw w wf x xs
  ... | no w′≢ε = restrict‴ aw w wf w′ w′≤w w′≢ε x xs

  restrict′ : 𝑆 → ∀ w → Acc _≺_ w → Forest A → ⟅ A ⟆ → ⟅ A ⟆
  restrict′ aw w a [] zs = zs
  restrict′ aw w a (x ∷ xs) zs = restrict″ aw w a x (restrict′ aw w a xs zs)

restrict : 𝑆 → Forest A → ⟅ A ⟆
restrict w x = restrict′ ε w (≺-wf w) x ⟅⟆

open import HITs.SetQuotients

UpTo : Forest A → Forest A → Type _
UpTo xs ys = ∀ w → restrict w xs ≡ restrict w ys

Heap : Type a → Type a
Heap A = Forest A / UpTo

-- -- open import Cubical.HITs.SetQuotients using (rec2)

-- -- ++-lhs : (xs ys zs : Heap′ A) → UpTo xs ys → UpTo (xs ++ zs) (ys ++ zs)
-- -- ++-lhs xs ys zs r w = let p = r w in {!!}

-- -- ++-rhs : (xs ys zs : Heap′ A) → UpTo ys zs → UpTo (xs ++ ys) (xs ++ zs)
-- -- ++-rhs xs ys zs r w = let p = r w in {!!}

-- -- _++H_ : Heap A → Heap A → Heap A
-- -- _++H_ = rec2 squash/ (λ xs ys → [ xs ++ ys ]) (λ xs ys zs r → eq/ _ _ (++-lhs xs ys zs r)) λ xs ys zs r → eq/ _ _ (++-rhs xs ys zs r)

-- -- -- -- Heap′ : Type a → Type a
-- -- -- -- Heap′ A = List (A ×)




-- -- -- data Heap (A : Type a) : Type a where
-- -- --   [_]    : ⟅ Tree A (Heap A) ⟆ → Heap A
-- -- --   flat/  : (xs : ⟅ Tree A ⟅ Tree A (Heap A) ⟆ ⟆)
-- -- --          → [ (do x ← xs ; (ε , root x ◁ [ ⟅⟆ ]) ∷ rest x) ] ≡ [ map (map-rest [_]) xs ]
    
  
