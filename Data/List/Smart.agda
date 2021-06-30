{-# OPTIONS --cubical --safe #-}

module Data.List.Smart where

open import Prelude




open import Data.Nat.Properties using (_≡ᴮ_; complete-==)

infixr 5 _∷′_ _++′_
data List {a} (A : Type a) : Type a where
  []′ : List A
  _∷′_ : A → List A → List A
  _++′_ : List A → List A → List A

sz′ : List A → ℕ → ℕ
sz′ []′ k = k
sz′ (x ∷′ xs) k = k
sz′ (xs ++′ ys) k = suc (sz′ xs (sz′ ys k))

sz : List A → ℕ
sz []′ = zero
sz (x ∷′ xs) = zero
sz (xs ++′ ys) = sz′ xs (sz ys)

_HasSize_ : List A → ℕ → Type
xs HasSize n = T (sz xs ≡ᴮ n)

data ListView {a} (A : Type a) : Type a where
  Nil : ListView A
  Cons : A → List A → ListView A

viewˡ : List A → ListView A
viewˡ xs = go xs (sz xs) (complete-== (sz xs))
  where
  go : (xs : List A) → (n : ℕ) → xs HasSize n → ListView A
  go  []′                  n       p = Nil
  go  (x ∷′ xs)            n       p = Cons x xs
  go  ((x ∷′ xs) ++′ ys)   n       p = Cons x (xs ++′ ys)
  go  ([]′ ++′ ys)         n       p = go ys n p
  go  ((xs ++′ ys) ++′ zs) (suc n) p = go (xs ++′ (ys ++′ zs)) n p
