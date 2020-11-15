{-# OPTIONS --cubical --postfix-projections --safe #-}

open import Relation.Binary
open import Prelude hiding (tt)

module Data.List.Sort.MergeSort {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open import Relation.Binary.Construct.LowerBound totalOrder
open import Data.List.Sort.Sorted totalOrder
open import Data.List.Sort.InsertionSort totalOrder

open TotalOrder totalOrder renaming (refl to refl-≤)
open TotalOrder lb-ord renaming (≤-trans to ⌊trans⌋) using ()

open import Data.List
open import Data.Unit.UniversePolymorphic as Poly using (tt)
open import Data.List.Relation.Binary.Permutation
open import Function.Isomorphism
open import Data.Fin
open import Data.List.Membership

mutual
  merge : List E → List E → List E
  merge = foldr mergeˡ id

  mergeˡ :  E → (List E → List E) → List E → List E
  mergeˡ x xs [] = x ∷ xs []
  mergeˡ x xs (y ∷ ys) = merge⁺ x xs y ys (x ≤ᵇ y)

  merge⁺ :  E → (List E → List E) → E → List E → Bool → List E
  merge⁺ x xs y ys true  = x ∷ xs (y ∷ ys)
  merge⁺ x xs y ys false = y ∷ mergeˡ x xs ys

open import Algebra

cmp-≤ : ∀ x y → x ≤ y → (x ≤ᵇ y) ≡ true
cmp-≤ x y x≤y with x ≤? y
cmp-≤ x y x≤y | yes _ = refl
cmp-≤ x y x≤y | no x≰y = ⊥-elim (x≰y x≤y)

cmp-≰ : ∀ x y → x ≰ y → (x ≤ᵇ y) ≡ false
cmp-≰ x y x≰y with x ≤? y
cmp-≰ x y x≰y | yes x≤y = ⊥-elim (x≰y x≤y)
cmp-≰ x y x≰y | no _    = refl

merge-idʳ : ∀ xs → merge xs [] ≡ xs
merge-idʳ [] = refl
merge-idʳ (x ∷ xs) = cong (x ∷_) (merge-idʳ xs)

open import Path.Reasoning
open import Data.List.Properties

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
  cong (merge⁺ y (merge (mergeˡ x (merge xs) ys)) z zs) (cmp-≰ y z y≰z) ;
  cong (z ∷_) (cong (λ xy → merge (merge⁺ x (merge xs) y ys xy) zs) (sym (cmp-≰ x y x≰y)) ; r) ;
  cong (merge⁺ x (merge xs) z (mergeˡ y (merge ys) zs)) (sym (cmp-≰ x z (<⇒≱ (<-trans (≰⇒> y≰z) (≰⇒> x≰y)))))
... | _ | r | _ | no x≰y | yes y≤z =
  cong (merge⁺ y (merge (mergeˡ x (merge xs) ys)) z zs) (cmp-≤ y z y≤z) ;
  cong (y ∷_) r ;
  cong (merge⁺ x (merge xs) y (merge ys (z ∷ zs))) (sym (cmp-≰ x y x≰y))
... | r | _ | _ | yes x≤y | yes y≤z =
  cong (merge⁺ x (merge (merge xs (y ∷ ys))) z zs) (cmp-≤ x z (≤-trans x≤y y≤z)) ;
  cong (x ∷_) (r ; cong (merge xs) (cong (merge⁺ y (merge ys) z zs) (cmp-≤ y z y≤z))) ;
  cong (merge⁺ x (merge xs) y (merge ys (z ∷ zs))) (sym (cmp-≤ x y x≤y))
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | rx≤z | _ | rx≰z | yes x≤y | no y≰z with x ≤? z
... | no  x≰z = cong (z ∷_) (cong (λ xy → merge (merge⁺ x (merge xs) y ys xy) zs) (sym (cmp-≤ x y x≤y)) ; rx≰z)
... | yes x≤z = cong (x ∷_) (rx≤z ; cong (merge xs) (cong (merge⁺ y (merge ys) z zs) (cmp-≰ y z y≰z)))

open import TreeFold

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
