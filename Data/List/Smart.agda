{-# OPTIONS --cubical --safe #-}

module Data.List.Smart where

open import Prelude
open import Data.Nat.Properties using (_≡ᴮ_; complete-==)

infixr 5 _∷′_ _++′_
data List {a} (A : Type a) : Type a where
  []′ : List A
  _∷′_ : A → List A → List A
  _++′_ : List A → List A → List A

mutual
  sz : List A → ℕ → ℕ
  sz []′ k = k
  sz (x ∷′ xs) k = k
  sz (xs ++′ ys) k = sz′ xs (sz ys k)

  sz′ : List A → ℕ → ℕ
  sz′ []′ k = k
  sz′ (x ∷′ xs) k = k
  sz′ (xs ++′ ys) k = suc (sz′ xs (sz′ ys k))

_HasSize_ : List A → ℕ → Type₀
xs HasSize n = T (sz xs zero ≡ᴮ n)

data ListView {a} (A : Type a) : Type a where
  Nil : ListView A
  Cons : A → List A → ListView A

reassoc : List A → ListView A
reassoc xs = go (sz xs zero) xs (complete-== (sz xs zero))
  where
  go : ∀ n → (xs : List A) → xs HasSize n → ListView A
  go n       []′                  p = Nil
  go n       (x ∷′ xs)            p = Cons x xs
  go n       ((x ∷′ xs) ++′ ys)   p = Cons x (xs ++′ ys)
  go n       ([]′ ++′ ys)         p = go n ys p
  go (suc n) ((xs ++′ ys) ++′ zs) p = go n (xs ++′ (ys ++′ zs)) p

  -- reassoc₁ : List A → List A → List A
  -- reassoc₁ []′ ys = reassoc ys
  -- reassoc₁ (x ∷′ xs) ys = x ∷′ (xs ++′ ys)
  -- reassoc₁ (xs ++′ ys) zs = reassoc₁ xs (ys ++′ zs)
