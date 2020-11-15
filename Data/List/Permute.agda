{-# OPTIONS --cubical --safe #-}

module Data.List.Permute where

open import Prelude
open import Data.Nat
open import Data.Nat.Properties using (_≤ᴮ_)

infixr 5 _∹_∷_
data Premuted {a} (A : Type a) : Type a where
 [] : Premuted A
 _∹_∷_ : ℕ → A → Premuted A → Premuted A

mutual
  merge : Premuted A → Premuted A → Premuted A
  merge [] = id
  merge (n ∹ x ∷ xs) = mergeˡ n x (merge xs)

  mergeˡ : ℕ → A → (Premuted A → Premuted A) → Premuted A → Premuted A
  mergeˡ i x xs [] = i ∹ x ∷ xs []
  mergeˡ i x xs (j ∹ y ∷ ys) = merge⁺ i x xs j y ys (i ≤ᴮ j)

  merge⁺ : ℕ → A → (Premuted A → Premuted A) → ℕ → A → Premuted A → Bool → Premuted A
  merge⁺ i x xs j y ys true  = i ∹ x ∷ xs ((j ∸ i) ∹ y ∷ ys)
  merge⁺ i x xs j y ys false = j ∹ y ∷ mergeˡ ((i ∸ j) ∸ 1) x xs ys

merge-idʳ : (xs : Premuted A) → merge xs [] ≡ xs
merge-idʳ [] = refl
merge-idʳ (i ∹ x ∷ xs) = cong (i ∹ x ∷_) (merge-idʳ xs)

-- open import Algebra

-- merge-assoc : Associative (merge {A = A})
-- merge-assoc [] ys zs = refl
-- merge-assoc (i ∹ x ∷ xs) [] zs = cong (flip merge zs) (merge-idʳ (i ∹ x ∷ xs))
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) [] = merge-idʳ (merge (i ∹ x ∷ xs) (j ∹ y ∷ ys)) ; sym (cong (merge (i ∹ x ∷ xs)) (merge-idʳ (j ∹ y ∷ ys)))
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) with i ≤ᴮ j | T? (i ≤ᴮ j) | j ≤ᴮ k | T? (j ≤ᴮ k)
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true | no i≰j | _ | _ = ⊥-elim (i≰j tt)
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | _ | _ | true | no j≰k = ⊥-elim (j≰k tt)
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true  | yes i≤j | false | no  j≰k = {!!}
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true  | yes i≤j | true  | yes j≤k = {!!}
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | false | no  i≰j | false | no  j≰k = {!!}
-- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | false | no  i≰j | true  | yes j≤k = {!!}

-- -- merge-assoc (x ∷ xs) [] zs = cong (flip merge zs) (merge-idʳ (x ∷ xs))
-- -- merge-assoc (x ∷ xs) (y ∷ ys) [] = 
-- -- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) with (j <ᴮ i) | (k <ᴮ j)
-- -- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | false | false = {!!}
-- -- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | false | true = {!!}
-- -- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true | false = {!!}
-- -- merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true | true = {!!}
