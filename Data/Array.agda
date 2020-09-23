{-# OPTIONS --cubical --safe #-}

module Data.Array where

open import Data.Binary
open import Prelude

private
  variable
    ns : 𝔹

infixr 5 _∷₁_ _∷₂_ _∷_

data Array {a} (A : Type a) : 𝔹 → Type a where
  [] : Array A 0ᵇ
  _∷₁_ : A → Array (A × A) ns → Array A (1ᵇ ns)
  _∷₂_ : A × A → Array (A × A) ns → Array A (2ᵇ ns)

_∷_ : A → Array A ns → Array A (inc ns)
x  ∷ [] = x ∷₁ []
x₁ ∷ x₂ ∷₁ xs = (x₁ , x₂) ∷₂ xs
x₁ ∷ x₂ ∷₂ xs = x₁ ∷₁ x₂ ∷ xs

open import Data.Binary.Order

mutual
  index : ∀ is {js} → Array A js → is < js → A
  index 0ᵇ      (x ∷₁ xs) p = x
  index 0ᵇ      (x ∷₂ xs) p = fst x
  index (1ᵇ is) xs        p = index₂1ᵇ is xs p
  index (2ᵇ is) (x ∷₁ xs) p = snd (index is xs p)
  index (2ᵇ is) (x ∷₂ xs) p = fst (index is xs p)

  index₂1ᵇ : ∀ is {js} → Array A js → 1ᵇ is < js → A
  index₂1ᵇ is      (x ∷₁ xs) p = fst (index is xs p)
  index₂1ᵇ 0ᵇ      (x ∷₂ xs) p = snd x
  index₂1ᵇ (1ᵇ is) (x ∷₂ xs) p = snd (index₃ is xs p)
  index₂1ᵇ (2ᵇ is) (x ∷₂ xs) p = snd (index₂2ᵇ is xs p)

  index₂2ᵇ : ∀ is {js} → Array A js → 2ᵇ is ≤ js → A
  index₂2ᵇ is      (x ∷₁ xs) p = fst (index is xs p)
  index₂2ᵇ 0ᵇ      (x ∷₂ xs) p = snd x
  index₂2ᵇ (1ᵇ is) (x ∷₂ xs) p = snd (index₃ is xs p)
  index₂2ᵇ (2ᵇ is) (x ∷₂ xs) p = snd (index₂2ᵇ is xs p)

  index₃ : ∀ is {js} → Array A js → 1ᵇ is ≤ js → A
  index₃ 0ᵇ      (x ∷₁ xs) p = x
  index₃ 0ᵇ      (x ∷₂ xs) p = fst x
  index₃ (1ᵇ is) (x ∷₁ xs) p = snd (index₃ is xs p)
  index₃ (1ᵇ is) (x ∷₂ xs) p = fst (index₃ is xs p)
  index₃ (2ᵇ is) (x ∷₁ xs) p = snd (index₂2ᵇ is xs p)
  index₃ (2ᵇ is) (x ∷₂ xs) p = fst (index₂2ᵇ is xs p)

index? : 𝔹 → Array A ns → Maybe A
index? {ns = ns} is xs with T? (is <ᴮ ns)
... | no  _ = nothing
... | yes p = just (index is xs p)

_!_ : ∀ {js} → Array A js → ∀ is → { p : is < js } → A
_!_ xs is {p} = index is xs p

-- open import Data.Binary.Literals
-- open import Data.Nat.Literals
-- open import Literals.Number

-- e : ℕ
-- e = (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ! 3


foldr : (A → B → B) → B → Array A ns → B
foldr f b [] = b
foldr f b (x ∷₁ xs) = f x (foldr (λ { (x₁ , x₂) b → f x₁ (f x₂ b) }) b xs)
foldr f b ((x₁ , x₂) ∷₂ xs) = f x₁ (f x₂ (foldr (λ { (x₁ , x₂) b → f x₁ (f x₂ b)}) b xs))

import Data.Nat as ℕ

foldrP : ∀ {p} (P : ℕ → Type p) → (∀ {n} → A → P n → P (suc n)) → P zero → Array A ns → P ⟦ ns ⇓⟧
foldrP P f b [] = b
foldrP P f b (x ∷₁ xs) = f x (foldrP (λ n → P (n ℕ.* 2)) (λ { (x₁ , x₂) b → f x₁ (f x₂ b) }) b xs)
foldrP P f b ((x₁ , x₂) ∷₂ xs) = f x₁ (f x₂ (foldrP (λ n → P (n ℕ.* 2)) (λ { (x₁ , x₂) b → f x₁ (f x₂ b)}) b xs))

-- upTo : ∀ n → Array ℕ ⟦ n ⇑⟧
-- upTo n = go n zero
--   where
--   go : ∀ n m → Array ℕ ⟦ n ⇑⟧
--   go zero    m = []
--   go (suc n) m = m ∷ go n (suc m)

-- import Data.List as List
-- import Data.Nat.Properties as ℕ

-- index-test : ℕ → Type₀
-- index-test n = List.map (λ i → index? ⟦ i ⇑⟧ arr) nums ≡ List.map just nums
--   where
--   arr : Array ℕ ⟦ n ⇑⟧
--   arr = upTo n

--   nums : List.List ℕ
--   nums = 0 List.⋯ ℕ.pred n

-- _ : index-test 33
-- _ = refl
