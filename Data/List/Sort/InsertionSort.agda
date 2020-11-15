{-# OPTIONS --cubical --postfix-projections --safe #-}

open import Relation.Binary
open import Prelude hiding (tt)

module Data.List.Sort.InsertionSort {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open import Relation.Binary.Construct.LowerBound totalOrder
open import Data.List.Sort.Sorted totalOrder

open TotalOrder totalOrder renaming (refl to refl-≤)
open TotalOrder lb-ord renaming (≤-trans to ⌊trans⌋) using ()

open import Data.List
open import Data.Unit.UniversePolymorphic as Poly using (tt)
open import Data.List.Relation.Binary.Permutation
open import Function.Isomorphism
open import Data.Fin
open import Data.List.Membership

private variable lb : ⌊∙⌋

insert : E → List E → List E
insert x [] = x ∷ []
insert x (y ∷ xs) with x ≤ᵇ y
... | true  = x ∷ y ∷ xs
... | false = y ∷ insert x xs

insert-sort : List E → List E
insert-sort = foldr insert []

insert-sorts : ∀ x xs → lb ≤⌊ x ⌋ → SortedFrom lb xs → SortedFrom lb (insert x xs)
insert-sorts x [] lb≤x Pxs = lb≤x , tt
insert-sorts x (y ∷ xs) lb≤x (lb≤y , Sxs) with x ≤? y
... | yes x≤y = lb≤x , x≤y , Sxs
... | no  x≰y = lb≤y , insert-sorts x xs (<⇒≤ (≰⇒> x≰y)) Sxs

sort-sorts : ∀ xs → Sorted (insert-sort xs)
sort-sorts [] = tt
sort-sorts (x ∷ xs) = insert-sorts x (insert-sort xs) tt (sort-sorts xs)

insert-perm : ∀ x xs → insert x xs ↭ x ∷ xs
insert-perm x [] = reflₚ
insert-perm x (y ∷ xs) with x ≤ᵇ y
... | true  = consₚ x reflₚ
... | false = consₚ y (insert-perm x xs) ⟨ transₚ ⟩ swapₚ y x xs

sort-perm : ∀ xs → insert-sort xs ↭ xs
sort-perm [] = reflₚ {xs = []}
sort-perm (x ∷ xs) = insert-perm x (insert-sort xs) ⟨ transₚ {xs = insert x (insert-sort xs)} ⟩ consₚ x (sort-perm xs)


perm-invar : ∀ xs ys → xs ↭ ys → insert-sort xs ≡ insert-sort ys
perm-invar xs ys xs⇔ys =
  perm-same
    (insert-sort xs)
    (insert-sort ys)
    (sort-sorts xs)
    (sort-sorts ys)
    (λ k → sort-perm xs k ⟨ trans-⇔ ⟩ xs⇔ys k ⟨ trans-⇔ ⟩ sym-⇔ (sort-perm ys k))
