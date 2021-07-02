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

mutual
  merge : List E → List E → List E
  merge = foldr mergeˡ id

  mergeˡ :  E → (List E → List E) → List E → List E
  mergeˡ x xs []       = x ∷ xs []
  mergeˡ x xs (y ∷ ys) = merge⁺ x xs y ys (x ≤ᵇ y)

  merge⁺ :  E → (List E → List E) → E → List E → Bool → List E
  merge⁺ x xs y ys = bool′ (y ∷ mergeˡ x xs ys) (x ∷ xs (y ∷ ys))

merge-idʳ : ∀ xs → merge xs [] ≡ xs
merge-idʳ [] = refl
merge-idʳ (x ∷ xs) = cong (x ∷_) (merge-idʳ xs)

merge-assoc : Associative merge
merge-assoc []       ys zs = refl
merge-assoc (x ∷ xs) [] zs = cong (λ xs′ → mergeˡ x (merge xs′) zs) (merge-idʳ xs)
merge-assoc (x ∷ xs) (y ∷ ys) [] = merge-idʳ (merge (x ∷ xs) (y ∷ ys)) ; cong (merge (x ∷ xs)) (sym (merge-idʳ (y ∷ ys)))
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs)
  with merge-assoc xs (y ∷ ys) (z ∷ zs)
     | merge-assoc (x ∷ xs) ys (z ∷ zs)
     | merge-assoc (x ∷ xs) (y ∷ ys) zs
     | x ≤? y
     | y ≤? z
... | _ | _ | r | no x≰y | no y≰z =
  cong (merge⁺ y (merge (mergeˡ x (merge xs) ys)) z zs) (from-reflects false (y ≤? z) y≰z) ;
  cong (z ∷_) (cong (λ xy → merge (merge⁺ x (merge xs) y ys xy) zs) (sym (from-reflects false (x ≤? y) x≰y)) ; r) ;
  cong (merge⁺ x (merge xs) z (mergeˡ y (merge ys) zs)) (sym (from-reflects false (x ≤? z) (<⇒≱ (<-trans (≰⇒> y≰z) (≰⇒> x≰y)))))
... | _ | r | _ | no x≰y | yes y≤z =
  cong (merge⁺ y (merge (mergeˡ x (merge xs) ys)) z zs) (from-reflects true (y ≤? z) y≤z) ;
  cong (y ∷_) r ;
  cong (merge⁺ x (merge xs) y (merge ys (z ∷ zs))) (sym (from-reflects false (x ≤? y) x≰y))
... | r | _ | _ | yes x≤y | yes y≤z =
  cong (merge⁺ x (merge (merge xs (y ∷ ys))) z zs) (from-reflects true (x ≤? z) (≤-trans x≤y y≤z)) ;
  cong (x ∷_) (r ; cong (merge xs) (cong (merge⁺ y (merge ys) z zs) (from-reflects true (y ≤? z) y≤z))) ;
  cong (merge⁺ x (merge xs) y (merge ys (z ∷ zs))) (sym (from-reflects true (x ≤? y) x≤y))
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | rx≤z | _ | rx≰z | yes x≤y | no y≰z with x ≤? z
... | no  x≰z = cong (z ∷_) (cong (λ xy → merge (merge⁺ x (merge xs) y ys xy) zs) (sym (from-reflects true (x ≤? y) x≤y)) ; rx≰z)
... | yes x≤z = cong (x ∷_) (rx≤z ; cong (merge xs) (cong (merge⁺ y (merge ys) z zs) (from-reflects false (y ≤? z) y≰z)))

merge-sort : List E → List E
merge-sort = treeFold merge [] ∘ map (_∷ [])

merge-insert : ∀ x xs → merge (x ∷ []) xs ≡ insert x xs
merge-insert x [] = refl
merge-insert x (y ∷ xs) with x ≤ᵇ y
... | false = cong (y ∷_) (merge-insert x xs)
... | true  = refl

merge≡insert-sort : ∀ xs → merge-sort xs ≡ insert-sort xs
merge≡insert-sort xs =
  merge-sort xs                      ≡⟨⟩
  treeFold merge [] (map (_∷ []) xs) ≡⟨ treeFoldHom merge [] merge-assoc (map (_∷ []) xs) ⟩
  foldr merge [] (map (_∷ []) xs)    ≡⟨ map-fusion merge [] (_∷ []) xs ⟩
  foldr (λ x → merge (x ∷ [])) [] xs ≡⟨ cong (λ f → foldr f [] xs) (funExt (funExt ∘ merge-insert)) ⟩
  foldr insert [] xs                 ≡⟨⟩
  insert-sort xs ∎
