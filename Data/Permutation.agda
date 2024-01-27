{-# OPTIONS --allow-unsolved-metas #-}

module Data.Permutation where

open import Prelude
open import Data.List
open import Data.Nat.Properties renaming (discreteℕ to _≟_)
open import Data.Nat using (_+_)
open import Path.Reasoning

Swaps : Type
Swaps = List (ℕ × ℕ)

unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
unflatten-alg x y k n = ((n + x) , suc (n + x + y)) ∷ k (suc n + x)

unflatten : Swaps → Swaps
unflatten xs = foldr (uncurry unflatten-alg) (const []) xs 0

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

swap-suc : ∀ x y z → swap (suc x) (suc y) (suc z) ≡ suc (swap x y z)
swap-suc x y z with x ≟ z | suc x ≟ suc z | y ≟ z | suc y ≟ suc z
... | yes xz | yes sxz | _ | _ = refl
... | no  xz | yes sxz | _ | _ = ⊥-elim (xz (suc-inj sxz)) 
... | yes xz | no sxz | _ | _ = ⊥-elim (sxz (cong suc xz))
... | _ | _ | no yz | yes syz = ⊥-elim (yz (suc-inj syz))
... | _ | _ | yes yz | no syz = ⊥-elim (syz (cong suc yz))
... | no  xz | no sxz | yes yz | yes syz = refl
... | no  xz | no sxz | no yz | no syz = refl

swap-id : ∀ x y → swap x x y ≡ y
swap-id x y with x ≟ y
... | no _ = refl
... | yes x≡y = x≡y

perm : Swaps → ℕ → ℕ
perm = flip (foldl (flip (uncurry swap)))

ep : Swaps
ep = ((2 , 1) ∷ (1 , 3) ∷ (1 , 0) ∷ [])

perm-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
perm-alg zero    y k zero    = suc (k y)
perm-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
perm-alg (suc x) y k zero    = zero
perm-alg (suc x) y k (suc z) = suc (perm-alg x y k z)

perm′ : Swaps → ℕ → ℕ
perm′ = foldr (uncurry perm-alg) id

prop : (xs : Swaps) (n : ℕ) → Type
prop xs n = perm′ xs n ≡ perm (unflatten xs) n

open import Data.List.Properties

-- foldr (λ x k xs → k (uncurry swap x xs)) id (foldr (uncurry unflatten-alg) (const []) xs 0) n
-- 
-- unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
-- unflatten-alg x y k n = ((n + x) , suc (n + x + y)) ∷ k (suc n + x)

swap-unf-alg : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
swap-unf-alg x y k a n = k (suc a + x) (swap (a + x) (suc (a + x + y)) n)

swap-unf′ : Swaps → ℕ → ℕ → ℕ
swap-unf′ = foldr (uncurry swap-unf-alg) (const id)

swap-unflatten : Swaps → ℕ → ℕ
swap-unflatten xs = swap-unf′ xs 0

swap-unflatten-lemma : ∀ xs m n → swap-unf′ xs m n ≡ foldr (λ x k xs → k (uncurry swap x xs)) id (foldr (uncurry unflatten-alg) (const []) xs m) n
swap-unflatten-lemma [] m n = refl
swap-unflatten-lemma (x ∷ xs) m n = cong (λ e → uncurry swap-unf-alg x e m n) (funExt λ m → funExt (swap-unflatten-lemma xs m))

open import Data.Nat

shft : ℕ → ℕ × ℕ → ℕ × ℕ
shft m = map-Σ (m +_) (m +_)

perm″ : ℕ → Swaps → ℕ → ℕ
perm″ m = foldr (uncurry perm-alg ∘ shft m) id

-- perm-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
-- perm-alg zero    y k zero    = suc (k y)
-- perm-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
-- perm-alg (suc x) y k zero    = zero
-- perm-alg (suc x) y k (suc z) = suc (perm-alg x y k z)

perm″-suc : ∀ m n xs → suc (perm″ m xs n) ≡ perm″ (suc m) xs (suc n)
perm″-suc m n [] = refl
perm″-suc m n ((x , y) ∷ xs) =
  suc (perm″ m ((x , y) ∷ xs) n) ≡⟨⟩
  suc (uncurry perm-alg (shft m (x , y)) (perm″ m xs) n) ≡⟨⟩
  suc (perm-alg (m + x) (    m + y) (perm″      m  xs) n) ≡⟨ {!!} ⟩
  suc (perm-alg (m + x) (suc m + y) (perm″ (suc m) xs) n) ≡⟨⟩
  perm-alg (suc m + x) (suc m + y) (perm″ (suc m) xs) (suc n) ≡⟨⟩
  uncurry perm-alg (shft (suc m) (x , y)) (perm″ (suc m) xs) (suc n) ≡⟨⟩
  perm″ (suc m) ((x , y) ∷ xs) (suc n) ∎

-- this does not hold
lemma₂ : ∀ x y xs m n → perm-alg x (suc y) (perm″ (suc m) xs) n ≡ perm-alg x y (perm″ m xs) n
lemma₂ zero y xs m zero = {!refl!}
lemma₂ zero y xs m (suc n) = {!!}
lemma₂ (suc x) y xs m zero = {!!}
lemma₂ (suc x) y xs m (suc n) = {!!}

lemma₁ : ∀ x y xs m n → perm-alg (m + x) (m + y) (perm″ m xs) n ≡
              perm″ (suc m + x) xs (swap (m + x) (suc (m + x + y)) n)
lemma₁ zero y xs zero zero = {!!} -- holds
lemma₁ zero y xs zero (suc n) = {!!} -- holds
lemma₁ (suc x) y xs zero zero = {!!} -- holds
lemma₁ (suc x) y xs zero (suc n) = {!!}  -- probably holds
lemma₁ x y xs (suc m) zero = {!!} -- holds
lemma₁ x y xs (suc m) (suc n) =
  cong suc ({!!} ; lemma₁ x y xs m n)
  ; perm″-suc (suc (m + x)) (swap (m + x) (suc (m + x + y)) n) xs ; sym (cong (perm″ (suc (suc (m + x))) xs) (swap-suc (m + x) (suc (m + x + y)) n))

perm-swap-unflatten : ∀ xs m n → perm″ m xs n ≡ swap-unf′ xs m n
perm-swap-unflatten [] m n = refl
perm-swap-unflatten ((x , y) ∷ xs) m n =
  perm-alg (m + x) (m + y) (perm″ m xs) n ≡⟨ lemma₁ x y xs m n ⟩
  perm″ (suc m + x) xs (swap (m + x) (suc (m + x + y)) n) ≡⟨ perm-swap-unflatten xs _ _ ⟩
  swap-unf′ xs (suc m + x) (swap (m + x) (suc (m + x + y)) n) ≡⟨⟩
  swap-unf-alg x y (swap-unf′ xs) m n ∎

-- swaps-compress : ∀ xs n → perm′ xs n ≡ perm (unflatten xs) n
-- swaps-compress xs n =
--   perm′ xs n
--     ≡⟨ perm-swap-unflatten xs 0 n ⟩
--   foldr (uncurry swap-unf-alg) (const id) xs 0 n
--     ≡⟨ swap-unflatten-lemma xs 0 n ⟩
--   foldr (λ x k xs → k (uncurry swap x xs)) id (foldr (uncurry unflatten-alg) (const []) xs 0) n
--     ≡⟨⟩
--   foldr (λ x k xs → k (uncurry swap x xs)) id (unflatten xs) n
--     ≡˘⟨ foldl-is-foldr (flip (uncurry swap)) n (unflatten xs) ⟩
--   foldl (flip (uncurry swap)) n (unflatten xs) ≡⟨⟩
--   perm (unflatten xs) n ∎

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
