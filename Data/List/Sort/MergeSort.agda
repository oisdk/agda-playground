{-# OPTIONS --cubical --postfix-projections --safe #-}

open import Relation.Binary
open import Prelude

module Data.List.Sort.MergeSort {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open TotalOrder totalOrder hiding (refl)

open import Data.List.Sort.InsertionSort totalOrder using (insert; insert-sort)


open import Data.List
open import Data.List.Properties

open import TreeFold

open import Algebra
open import Relation.Nullary.Decidable.Properties using (from-reflects)
open import Path.Reasoning

mergeˡ :  E → (List E → List E) → List E → List E
mergeˡ x xs []       = x ∷ xs []
mergeˡ x xs (y ∷ ys) = if x ≤ᵇ y then x ∷ xs (y ∷ ys) else y ∷ mergeˡ x xs ys

_⋎_ : List E → List E → List E
_⋎_ = foldr mergeˡ id

merge-idʳ : ∀ xs → xs ⋎ [] ≡ xs
merge-idʳ [] = refl
merge-idʳ (x ∷ xs) = cong (x ∷_) (merge-idʳ xs)

merge-assoc : Associative _⋎_
merge-assoc []       ys zs = refl
merge-assoc (x ∷ xs) [] zs = cong (λ xs′ → mergeˡ x (xs′ ⋎_) zs) (merge-idʳ xs)
merge-assoc (x ∷ xs) (y ∷ ys) [] = merge-idʳ ((x ∷ xs) ⋎ (y ∷ ys)) ; cong ((x ∷ xs) ⋎_) (sym (merge-idʳ (y ∷ ys)))
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs)
  with merge-assoc xs (y ∷ ys) (z ∷ zs)
     | merge-assoc (x ∷ xs) ys (z ∷ zs)
     | merge-assoc (x ∷ xs) (y ∷ ys) zs
     | x ≤? y in x≤?y
     | y ≤? z in y≤?z
... | _ | _ | r | no x≰y | no y≰z rewrite y≤?z rewrite x≤?y =
  cong (z ∷_) r ;
  cong (bool′ _ _)
    (sym (from-reflects false (x ≤? z) (<⇒≱ ≲[ ≱[ y≰z ] ≲; ≱[ x≰y ] ])))
... | _ | r | _ | no  x≰y | yes y≤z rewrite y≤?z rewrite x≤?y = cong (y ∷_) r
... | r | _ | _ | yes x≤y | yes y≤z rewrite y≤?z rewrite x≤?y =
  cong (bool′ _ _)
    (from-reflects true (x ≤? z) (≤-trans x≤y y≤z)) ;
  cong (x ∷_) r
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | rx≤z | _ | rx≰z | yes x≤y | no y≰z with x ≤? z
... | no  x≰z rewrite x≤?y = cong (z ∷_) rx≰z
... | yes x≤z rewrite y≤?z = cong (x ∷_) rx≤z

merge-sort : List E → List E
merge-sort = treeFold _⋎_ [] ∘ map (_∷ [])

merge-insert : ∀ x xs → (x ∷ []) ⋎ xs ≡ insert x xs
merge-insert x [] = refl
merge-insert x (y ∷ xs) with x ≤ᵇ y
... | false = cong (y ∷_) (merge-insert x xs)
... | true  = refl

merge≡insert-sort : ∀ xs → merge-sort xs ≡ insert-sort xs
merge≡insert-sort xs =
  merge-sort xs                      ≡⟨⟩
  treeFold _⋎_ [] (map (_∷ []) xs)   ≡⟨ treeFoldHom _⋎_ [] merge-assoc (map (_∷ []) xs) ⟩
  foldr _⋎_ [] (map (_∷ []) xs)      ≡⟨ map-fusion _⋎_ [] (_∷ []) xs ⟩
  foldr (λ x → (x ∷ []) ⋎_) [] xs    ≡⟨ cong (λ f → foldr f [] xs) (funExt (funExt ∘ merge-insert)) ⟩
  foldr insert [] xs                 ≡⟨⟩
  insert-sort xs ∎
