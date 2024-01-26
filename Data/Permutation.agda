module Data.Permutation where

open import Prelude
open import Data.List
open import Data.Nat.Properties renaming (discreteℕ to _≟_)

Swaps : Type
Swaps = List (ℕ × ℕ)

swap : ℕ → ℕ → ℕ → ℕ
swap x y z =
  if does (x ≟ z) then y else
  if does (y ≟ z) then x else
  z

swap-lhs : ∀ x y → swap x y x ≡ y
swap-lhs x y with x ≟ x
... | no  x≢x = ⊥-elim (x≢x refl) 
... | yes x≡x = refl

swap-rhs : ∀ x y → swap x y y ≡ x
swap-rhs x y with x ≟ y
... | yes x≡y = sym x≡y
... | no  x≢y with y ≟ y
... | no  y≢y = ⊥-elim (y≢y refl)
... | yes y≡y = refl

swap-id : ∀ x y → swap x x y ≡ y
swap-id x y with x ≟ y
... | no _ = refl
... | yes x≡y = x≡y

perm : Swaps → ℕ → ℕ
perm = flip (foldl (flip (uncurry swap)))

data Perm : Type where
  <_> : Swaps → Perm
  eq : (x y : Swaps) → (∀ n → perm x n ≡ perm y n) → < x > ≡ < y >

_·_ : Perm → ℕ → ℕ
< x > · n = perm x n
eq x y e i · n = e n i

-- module _ (f : ℕ → ℕ → A → A) (b : A)
--          (unswap : ∀ n m x → f n m (f m n x) ≡ x)
--          (swapid : ∀ n x → f n n x ≡ x)
--          where

--   perm-id : (x : Swaps) → (∀ n → perm x n ≡ n) → foldr (uncurry f) b x ≡ b
--   perm-id [] p = refl
--   perm-id ((x , y) ∷ xs) p =
--     let h₁ = cong (perm xs) (sym (swap-rhs x y)) ; p y ⦂ perm xs x ≡ y
--         h₂ = cong (perm xs) (sym (swap-lhs x y)) ; p x ⦂ perm xs y ≡ x
--     in {!!}

--   foldr-perm : Perm → A
--   foldr-perm < xs > = foldr (uncurry f) b xs
--   foldr-perm (eq x y e i) = lemma x y e i
--     where
--     lemma : ∀ x y 
--           → (∀ n → perm x n ≡ perm y n)
--           → foldr (uncurry f) b x ≡ foldr (uncurry f) b y
--     lemma [] [] q = refl
--     lemma [] (x ∷ xs) q = {!!}
--     lemma (x ∷ x₁) [] q = {!!}
--     lemma (x ∷ x₁) (x₂ ∷ y) q = {!!}

-- -- open import Data.List.Syntax

-- -- _ : perm ( (1 , 2) ∷  (2 , 3) ∷ []) 1 ≡ 3
-- -- _ = refl
