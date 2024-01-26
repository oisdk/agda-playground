module Data.Permutation where

open import Prelude
open import Data.List
open import Data.Nat.Properties renaming (discreteℕ to _≟_)
open import Data.Nat using (_+_)

Swaps : Type
Swaps = List (ℕ × ℕ)

unflatten : Swaps → Swaps
unflatten = go 0
  where
  go : ℕ → Swaps → Swaps
  go n [] = []
  go n ((x , y) ∷ xs) = ((n + x) , suc (n + x + y)) ∷ go (suc n + x) xs

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

ep : Swaps
ep = ((2 , 1) ∷ (1 , 3) ∷ (1 , 0) ∷ [])

perm′ : Swaps → ℕ → ℕ
perm′ = foldr (uncurry f) id
  where
  f : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
  f zero    y k zero    = suc (k y)
  f zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
  f (suc x) y k zero    = zero
  f (suc x) y k (suc z) = suc (f x y k z)

prop : (xs : Swaps) (n : ℕ) → Type
prop xs n = perm′ xs n ≡ perm (unflatten xs) n

swaps-compress : ∀ xs n → perm′ xs n ≡ perm (unflatten xs) n
swaps-compress xs n = {!!}


-- e : ℕ → ℕ
-- e = perm ep


-- infix 4 _~ₚ_
-- _~ₚ_ : Swaps → Swaps → Type
-- x ~ₚ y = ∀ n → perm x n ≡ perm y n

-- data Perm : Type where
--   <_> : Swaps → Perm
--   eq : ∀ x y → x ~ₚ y → < x > ≡ < y >

-- _·_ : Perm → ℕ → ℕ
-- < x > · n = perm x n
-- eq x y e i · n = e n i

-- open import Data.List.Properties using (foldr-++)
-- open import Path.Reasoning

-- ~ₚ-++ : ∀ w x y z → w ~ₚ x → y ~ₚ z → w ++ y ~ₚ x ++ z
-- ~ₚ-++ ws xs ys zs p q n =
--   perm (ws ++ ys) n   ≡⟨ foldr-++ (uncurry swap) n ws ys ⟩
--   perm ws (perm ys n) ≡⟨ p (perm ys n) ⟩
--   perm xs (perm ys n) ≡⟨ cong (perm xs) (q n) ⟩
--   perm xs (perm zs n) ≡˘⟨ foldr-++ (uncurry swap) n xs zs ⟩
--   perm (xs ++ zs) n ∎

-- -- module _ (f : ℕ → ℕ → A → A) (b : A)
-- --          (unswap : ∀ n m x → f n m (f m n x) ≡ x)
-- --          (swapid : ∀ n x → f n n x ≡ x)
-- --          where

-- --   perm-id : (x : Swaps) → (∀ n → perm x n ≡ n) → foldr (uncurry f) b x ≡ b
-- --   perm-id [] p = refl
-- --   perm-id ((x , y) ∷ xs) p =
-- --     let h₁ = cong (perm xs) (sym (swap-rhs x y)) ; p y ⦂ perm xs x ≡ y
-- --         h₂ = cong (perm xs) (sym (swap-lhs x y)) ; p x ⦂ perm xs y ≡ x
-- --     in {!!}

-- --   foldr-perm : Perm → A
-- --   foldr-perm < xs > = foldr (uncurry f) b xs
-- --   foldr-perm (eq x y e i) = lemma x y e i
-- --     where
-- --     lemma : ∀ x y 
-- --           → (∀ n → perm x n ≡ perm y n)
-- --           → foldr (uncurry f) b x ≡ foldr (uncurry f) b y
-- --     lemma [] [] q = refl
-- --     lemma [] (x ∷ xs) q = {!!}
-- --     lemma (x ∷ x₁) [] q = {!!}
-- --     lemma (x ∷ x₁) (x₂ ∷ y) q = {!!}

-- -- -- open import Data.List.Syntax

-- -- -- _ : perm ( (1 , 2) ∷  (2 , 3) ∷ []) 1 ≡ 3
-- -- -- _ = refl
