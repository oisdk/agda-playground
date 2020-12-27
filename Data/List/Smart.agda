{-# OPTIONS --cubical --safe #-}

module Data.List.Smart where

open import Prelude

infixr 5 _∷′_ _++′_
data List {a} (A : Type a) : Type a where
  []′ : List A
  _∷′_ : A → List A → List A
  _++′_ : List A → List A → List A

data Viewˡ {a} (A : Type a) : Type a where
  []″  : Viewˡ A
  _∷″_ : A → List A → Viewˡ A


Assocd : List A → Type₀
Assocd []′ = ⊤
Assocd (x ∷′ xs) = ⊤
Assocd ([]′ ++′ ys) = Assocd ys
Assocd ((x ∷′ xs) ++′ ys) = ⊤
Assocd ((xs ++′ xs₁) ++′ ys) = ⊥

-- sz : List A → ℕ → ℕ
-- sz []′ n = n
-- sz (x ∷′ xs) n = suc (sz xs n)
-- sz (xs ++′ ys) n = sz xs (sz ys n)

-- viewˡ : List A → Viewˡ A
-- viewˡ []′         = []″
-- viewˡ (x  ∷′  xs) = x ∷″ xs
-- viewˡ ([]′ ++′ ys) = viewˡ ys
-- viewˡ ((x ∷′ xs) ++′ ys) = x ∷″ (xs ++′ ys)
-- viewˡ ((xs ++′ ys) ++′ zs) = viewˡ (xs ++′ (ys ++′ zs))
