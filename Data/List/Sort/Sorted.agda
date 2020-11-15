{-# OPTIONS --cubical --postfix-projections --safe #-}

open import Relation.Binary
open import Prelude hiding (tt)

module Data.List.Sort.Sorted {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open import Relation.Binary.Construct.LowerBound totalOrder

open TotalOrder totalOrder renaming (refl to refl-≤)
open TotalOrder lb-ord renaming (≤-trans to ⌊trans⌋) using ()

open import Data.List
open import Data.Unit.UniversePolymorphic as Poly using (tt)
open import Data.List.Relation.Binary.Permutation
open import Function.Isomorphism
open import Data.Fin
open import Data.List.Membership

private variable lb : ⌊∙⌋

Sorted-cons : E → (⌊∙⌋ → Type (r₁ ℓ⊔ r₂)) → ⌊∙⌋ → Type (r₁ ℓ⊔ r₂)
Sorted-cons x xs lb = (lb ≤⌊ x ⌋) × xs ⌊ x ⌋

SortedFrom : ⌊∙⌋ → List E → Type _
SortedFrom = flip (foldr Sorted-cons (const Poly.⊤))

Sorted : List E → Type _
Sorted = SortedFrom ⌊⊥⌋

ord-in : ∀ x xs → SortedFrom lb xs → x ∈ xs → lb ≤⌊ x ⌋
ord-in {lb = lb} x (x₁ ∷ xs) p (f0 , x∈xs) = subst (lb ≤⌊_⌋) x∈xs (p .fst)
ord-in {lb} x (y ∷ xs) p (fs n , x∈xs) = ⌊trans⌋ {lb} (p .fst) (ord-in x xs (p .snd) (n , x∈xs))

perm-head : ∀ {lbˣ lbʸ} x xs y ys → SortedFrom lbˣ (x ∷ xs) → SortedFrom lbʸ (y ∷ ys) → (x ∷ xs ↭ y ∷ ys) → x ≡ y
perm-head x xs y ys Sxs Sys xs⇔ys with xs⇔ys _ .inv (f0 , refl)
... | f0  , y∈xs = y∈xs
... | fs n , y∈xs with xs⇔ys _ .fun (f0 , refl)
... | f0  , x∈ys = sym x∈ys
... | fs m , x∈ys = antisym (ord-in y xs (Sxs .snd) (n , y∈xs)) (ord-in x ys (Sys .snd) (m , x∈ys))

perm-same : ∀ {lbˣ lbʸ} xs ys → SortedFrom lbˣ xs → SortedFrom lbʸ ys → xs ↭ ys → xs ≡ ys
perm-same [] [] Sxs Sys xs⇔ys = refl
perm-same [] (y ∷ ys) Sxs Sys xs⇔ys = ⊥-elim (xs⇔ys _ .inv (f0 , refl) .fst)
perm-same (x ∷ xs) [] Sxs Sys xs⇔ys = ⊥-elim (xs⇔ys _ .fun (f0 , refl) .fst)
perm-same {lbˣ} {lbʸ} (x ∷ xs) (y ∷ ys) Sxs Sys xs⇔ys =
  let h = perm-head {lbˣ} {lbʸ} x xs y ys Sxs Sys xs⇔ys
  in cong₂ _∷_ h
      (perm-same xs ys (Sxs .snd) (Sys .snd) (tailₚ x xs ys (subst (λ y′ → x ∷ xs ↭ y′ ∷ ys) (sym h) xs⇔ys)))

sorted-perm-eq : ∀ xs ys → Sorted xs → Sorted ys → xs ↭ ys → xs ≡ ys
sorted-perm-eq = perm-same
