{-# OPTIONS --cubical --postfix-projections --safe #-}

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
insert x (y ∷ xs) with x ≤ᵇ y
... | true  = x ∷ y ∷ xs
... | false = y ∷ insert x xs

insert-sort : List E → List E
insert-sort = foldr insert []

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

perm-invar : ∀ xs ys → xs ↭ ys → insert-sort xs ≡ insert-sort ys
perm-invar xs ys xs⇔ys =
  perm-same
    (insert-sort xs)
    (insert-sort ys)
    (sort-sorts xs)
    (sort-sorts ys)
    (λ k → sort-perm xs k ⟨ trans-⇔ ⟩ xs⇔ys k ⟨ trans-⇔ ⟩ sym-⇔ (sort-perm ys k))

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

merge-assoc : Associative merge
merge-assoc []       ys zs = refl
merge-assoc (x ∷ xs) [] zs = cong (λ xs′ → mergeˡ x (merge xs′) zs) (merge-idʳ xs)
merge-assoc (x ∷ xs) (y ∷ ys) [] = merge-idʳ (merge (x ∷ xs) (y ∷ ys)) ; cong (merge (x ∷ xs)) (sym (merge-idʳ (y ∷ ys)))
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) with merge-assoc xs (y ∷ ys) (z ∷ zs) | merge-assoc (x ∷ xs) ys (z ∷ zs) | merge-assoc (x ∷ xs) (y ∷ ys) zs | x ≤? y | y ≤? z
... | _ | _ | r | no x≰y | no y≰z = cong (merge⁺ y (merge (mergeˡ x (merge xs) ys)) z zs) (cmp-≰ y z y≰z) ;
                                    cong (z ∷_) (cong (λ xy → merge (merge⁺ x (merge xs) y ys xy) zs) (sym (cmp-≰ x y x≰y)) ; r) ;
                                    cong (merge⁺ x (merge xs) z (mergeˡ y (merge ys) zs)) (sym (cmp-≰ x z (<⇒≱ (<-trans (≰⇒> y≰z) (≰⇒> x≰y)))))
... | _ | r | _ | no x≰y | yes y≤z = cong (merge⁺ y (merge (mergeˡ x (merge xs) ys)) z zs) (cmp-≤ y z y≤z) ;
                                     cong (y ∷_) r ;
                                     cong (merge⁺ x (merge xs) y (merge ys (z ∷ zs))) (sym (cmp-≰ x y x≰y))
... | r | _ | _ | yes x≤y | yes y≤z = cong (merge⁺ x (merge (merge xs (y ∷ ys))) z zs) (cmp-≤ x z (≤-trans x≤y y≤z)) ;
                                      cong (x ∷_) (r ; cong (merge xs) (cong (merge⁺ y (merge ys) z zs) (cmp-≤ y z y≤z))) ;
                                      cong (merge⁺ x (merge xs) y (merge ys (z ∷ zs))) (sym (cmp-≤ x y x≤y))
merge-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) | rx≤z | _ | rx≰z | (yes x≤y) | (no y≰z) with x ≤? z
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

open import Path.Reasoning
open import Data.List.Properties

merge≡insert-sort : ∀ xs → merge-sort xs ≡ insert-sort xs
merge≡insert-sort xs =
  merge-sort xs                      ≡⟨⟩
  treeFold merge [] (map (_∷ []) xs) ≡⟨ treeFoldHom merge [] merge-assoc (map (_∷ []) xs) ⟩
  foldr merge [] (map (_∷ []) xs)    ≡⟨ map-fusion merge [] (_∷ []) xs ⟩
  foldr (λ x → merge (x ∷ [])) [] xs ≡⟨ cong (λ f → foldr f [] xs) (funExt (funExt ∘ merge-insert)) ⟩
  foldr insert [] xs                 ≡⟨⟩
  insert-sort xs ∎
