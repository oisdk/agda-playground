{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Relation.Binary
open import Prelude hiding (tt)

module Data.List.Sort {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open import Relation.Binary.Construct.LowerBound totalOrder

open TotalOrder totalOrder renaming (refl to refl-≤)
open TotalOrder lb-ord renaming (≤-trans to ⌊trans⌋) using ()

open import Data.List
open import Data.Unit.UniversePolymorphic as Poly using (tt)
open import Data.List.Relation.Binary.Permutation
open import Function.Isomorphism
open import Data.Fin
open import Data.List.Membership

insert : E → List E → List E
insert x [] = x ∷ []
insert x (y ∷ xs) with x ≤? y
... | inl  x≤y  = x  ∷ y ∷ xs
... | inr  y≤x  = y  ∷ insert x xs

sort : List E → List E
sort []        = []
sort (x ∷ xs)  = insert x (sort xs)

private variable lb : ⌊∙⌋

Sorted-cons : E → (⌊∙⌋ → Type (r₁ ℓ⊔ r₂)) → ⌊∙⌋ → Type (r₁ ℓ⊔ r₂)
Sorted-cons x xs lb = (lb ≤⌊ x ⌋) × xs ⌊ x ⌋

SortedFrom : ⌊∙⌋ → List E → Type _
SortedFrom = flip (foldr Sorted-cons (const Poly.⊤))

Sorted : List E → Type _
Sorted = SortedFrom ⌊⊥⌋

insert-sorts : ∀ x xs → lb ≤⌊ x ⌋ → SortedFrom lb xs → SortedFrom lb (insert x xs)
insert-sorts x [] lb≤x Pxs = lb≤x , tt
insert-sorts x (y ∷ xs) lb≤x (lb≤y , Sxs) with x ≤? y
... | inl x≤y = lb≤x , x≤y , Sxs
... | inr y≤x = lb≤y , insert-sorts x xs y≤x Sxs

sort-sorts : ∀ xs → Sorted (sort xs)
sort-sorts [] = tt
sort-sorts (x ∷ xs) = insert-sorts x (sort xs) tt (sort-sorts xs)

insert-perm : ∀ x xs → insert x xs ↭ x ∷ xs
insert-perm x [] = reflₚ
insert-perm x (y ∷ xs) with x ≤? y
... | inl x≤y = consₚ x reflₚ
... | inr y≤x = consₚ y (insert-perm x xs) ⟨ transₚ ⟩ swapₚ y x xs

sort-perm : ∀ xs → sort xs ↭ xs
sort-perm [] = reflₚ {xs = []}
sort-perm (x ∷ xs) = insert-perm x (sort xs) ⟨ transₚ {xs = insert x (sort xs)} ⟩ consₚ x (sort-perm xs)

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

perm-invar : ∀ xs ys → xs ↭ ys → sort xs ≡ sort ys
perm-invar xs ys xs⇔ys =
  perm-same
    (sort xs)
    (sort ys)
    (sort-sorts xs)
    (sort-sorts ys)
    (λ k → sort-perm xs k ⟨ trans-⇔ ⟩ xs⇔ys k ⟨ trans-⇔ ⟩ sym-⇔ (sort-perm ys k))

mutual
  merge : List E → List E → List E
  merge []       ys = ys
  merge (x ∷ xs) ys = mergeˡ x xs ys

  mergeˡ : E → List E → List E → List E
  mergeˡ x xs [] = x ∷ xs
  mergeˡ x xs (y ∷ ys) = merge⁺ x xs y ys (cmp x y)

  merge⁺ : E → List E → E → List E → Ord → List E
  merge⁺ x xs y ys LT = x ∷ mergeˡ y ys xs
  merge⁺ x xs y ys EQ = x ∷ y ∷ merge xs ys
  merge⁺ x xs y ys GT = y ∷ mergeˡ x xs ys

merge-idʳ : ∀ xs → merge xs [] ≡ xs
merge-idʳ [] = refl
merge-idʳ (x ∷ xs) = refl

open import Path.Reasoning

cmp-< : ∀ x y → x < y → cmp x y ≡ LT
cmp-< x y x<y with compare x y
cmp-< x y x<y | lt _ = refl
cmp-< x y x<y | eq x≡y = ⊥-elim (irrefl x<y x≡y)
cmp-< x y x<y | gt x>y = ⊥-elim (asym x<y x>y)

cmp-> : ∀ x y → y < x → cmp x y ≡ GT
cmp-> x y x>y with compare x y
cmp-> x y x>y | lt x<y = ⊥-elim (asym x<y x>y)
cmp-> x y x>y | eq x≡y = ⊥-elim (irrefl x>y (sym x≡y))
cmp-> x y x>y | gt _ = refl

cmp-≡ : ∀ x y → x ≡ y → cmp x y ≡ EQ
cmp-≡ x y x≡y with compare x y
cmp-≡ x y x≡y | lt x<y = ⊥-elim (irrefl x<y x≡y)
cmp-≡ x y x≡y | eq _ = refl
cmp-≡ x y x≡y | gt x>y = ⊥-elim (irrefl x>y (sym x≡y))

merge-comm : ∀ xs ys → merge xs ys ≡ merge ys xs
merge-comm [] [] = refl
merge-comm [] (x ∷ ys) = refl
merge-comm (x ∷ xs) [] = refl
merge-comm (x ∷ xs) (y ∷ ys) with compare x y
... | lt x<y = cong (merge⁺ y ys x xs) (sym (cmp-> y x x<y))
... | eq x≡y = cong₂ _∷_ x≡y (cong₂ _∷_ (sym x≡y) (merge-comm xs ys)) ; cong (merge⁺ y ys x xs) (sym (cmp-≡ y x (sym x≡y)))
... | gt x>y = cong (merge⁺ y ys x xs) (sym (cmp-< y x x>y))

-- merge-assoc : ∀ (xs ys zs : List E) →
--               merge (merge xs ys) zs ≡ merge xs (merge ys zs)
-- merge-assoc [] ys zs = refl
-- merge-assoc (x ∷ xs) [] zs = refl
-- merge-assoc (x ∷ xs) (y ∷ ys) [] = merge-idʳ (merge⁺ x xs y ys (cmp x y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) with compare x y | compare y z
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | yz with compare x z
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | lt y<z | lt x<z = cong (x ∷_) {!!} ; cong (merge⁺ x xs y (mergeˡ z zs ys)) (sym (cmp-< x y x<y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | eq y≡z | lt x<z = cong (x ∷_) {!!} ; cong (merge⁺ x xs y (z ∷ merge ys zs)) (sym (cmp-< x y x<y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | gt y>z | lt x<z = cong (x ∷_) {!!} ; cong (merge⁺ x xs z (mergeˡ y ys zs)) (sym (cmp-< x z x<z))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | lt y<z | eq x≡z = cong (x ∷_) {!!} ; cong (merge⁺ x xs y (mergeˡ z zs ys)) (sym (cmp-< x y x<y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | eq y≡z | eq x≡z = cong (x ∷_) {!!} ; cong (merge⁺ x xs y (z ∷ merge ys zs)) (sym (cmp-< x y x<y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | gt y>z | eq x≡z = cong (λ r → x ∷ z ∷ r) {!!} ; cong (merge⁺ x xs z (mergeˡ y ys zs)) (sym (cmp-≡ x z x≡z))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | lt y<z | gt x>z = ⊥-elim (asym x>z (<-trans x<y y<z))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | eq y≡z | gt x>z = ⊥-elim (irrefl (<-trans x>z x<y) (sym y≡z))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | lt x<y | gt y>z | gt x>z = cong (z ∷_) {!!} ; cong (merge⁺ x xs z (mergeˡ y ys zs)) (sym (cmp-> x z x>z))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | eq x≡y | lt y<z = cong (merge⁺ x (y ∷ merge xs ys) z zs) (cmp-< x z (subst (_< z) (sym x≡y) y<z)) ;
--                                                            cong (x ∷_) (cong (merge⁺ z zs y (merge xs ys)) (cmp-> z y y<z) ; cong (y ∷_) {!!}) ;
--                                                            cong (merge⁺ x xs y (mergeˡ z zs ys)) (sym (cmp-≡ x y x≡y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | eq x≡y | eq y≡z = cong (merge⁺ x (y ∷ merge xs ys) z zs) (cmp-≡ x z (x≡y ; y≡z)) ;
--                                                            cong (x ∷_) (cong₂ _∷_ (sym y≡z) {!!}) ;
--                                                            cong (merge⁺ x xs y (z ∷ merge ys zs)) (sym (cmp-≡ x y x≡y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | eq x≡y | gt y>z = cong (merge⁺ x (y ∷ merge xs ys) z zs) (cmp-> x z (subst (z <_) (sym x≡y) y>z)) ;
--                                                            cong (z ∷_) {!!} ;
--                                                            cong (merge⁺ x xs z (mergeˡ y ys zs)) (sym (cmp-> x z (subst (z <_) (sym x≡y) y>z)))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | gt x>y | lt y<z = cong (merge⁺ y (mergeˡ x xs ys) z zs) (cmp-< y z y<z) ;
--                                                            cong (y ∷_) {!!} ;
--                                                            cong (merge⁺ x xs y (mergeˡ z zs ys)) (sym (cmp-> x y x>y))
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | gt x>y | eq y≡z = {!!}
-- merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | gt x>y | gt y>z = {!!}
