{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary

module Data.AVLTree {k} {K : Type k} {r} (totalOrder : TotalOrder K r) where

open import Relation.Binary.Construct.Bounded totalOrder
open import Data.Nat using (_+_)
open TotalOrder totalOrder using (_≤?_)
open TotalOrder b-ord using () renaming (trans to ≤-trans; refl to ≤-refl)

private
  variable
    n m l : ℕ

data Bal : ℕ → ℕ → ℕ → Type₀ where
  ll : Bal (suc n) n (suc n)
  ee : Bal n n n
  rr : Bal n (suc n) (suc n)

balr : Bal n m l → Bal l n l
balr ll = ee
balr ee = ee
balr rr = ll

ball : Bal n m l → Bal m l l
ball ll = rr
ball ee = ee
ball rr = ee

private
  variable
    v : Level
    Val : K → Type v

data Tree {v} (Val : K → Type v) (lb ub : [∙]) : ℕ → Type (k ℓ⊔ r ℓ⊔ v) where
  leaf : (lb≤ub : lb [≤] ub) →
         Tree Val lb ub zero
  node : (key : K)
         (val : Val key)
         (bal : Bal n m l)
         (lchild : Tree Val lb [ key ] n)
         (rchild : Tree Val [ key ] ub m) →
         Tree Val lb ub (suc l)

private
  variable
    lb ub : [∙]

data Inc {t} (T : ℕ → Type t) (n : ℕ) : Type t where
  stay : T n       → Inc T n
  high : T (suc n) → Inc T n

rotʳ : (x : K) →
       (vl : Val x) →
       (ls : Tree Val lb [ x ] (2 + n)) →
       (rs : Tree Val [ x ] ub n) →
       Inc (Tree Val lb ub) (2 + n)
rotʳ y vl (node x v ll ls ls₁) rs = stay (node x v ee ls (node y vl ee ls₁ rs))
rotʳ y vl (node x v ee ls ls₁) rs = high (node x v rr ls (node y vl ll ls₁ rs))
rotʳ x xv (node y yv rr a (node z zv bl b c)) d = stay (node z zv ee (node y yv (balr bl) a b) (node x xv (ball bl) c d))

rotˡ : (x : K) → (xv : Val x) →
       (ls : Tree Val lb [ x ] n) →
       (rs : Tree Val [ x ] ub (2 + n)) →
       Inc (Tree Val lb ub) (2 + n)
rotˡ x xv ls (node y yv ee rs rs₁) = high (node y yv ll (node x xv rr ls rs) rs₁)
rotˡ x xv ls (node y yv rr rs rs₁) = stay (node y yv ee (node x xv ee ls rs) rs₁)
rotˡ y yv a (node x xv ll (node z zv bl b c) d) = stay (node z zv ee (node y yv (balr bl) a b) (node x xv (ball bl) c d))

insertWithin : (x : K) → Val x →
               (lb [≤] [ x ]) →
               ([ x ] [≤] ub) →
               (tr : Tree Val lb ub n) →
               Inc (Tree Val lb ub) n
insertWithin x xv lb≤x x≤ub (leaf lb≤ub) =
  high (node x xv ee (leaf lb≤x) (leaf x≤ub))
insertWithin x xv lb≤x x≤ub (node y yv bal ls rs) with x ≤? y
... | inl x≤y with insertWithin x xv lb≤x x≤y ls
... | stay ls′ = stay (node y yv bal ls′ rs)
... | high ls′ with bal
... | ll = rotʳ y yv ls′ rs
... | ee = high (node y yv ll ls′ rs)
... | rr = stay (node y yv ee ls′ rs)
insertWithin x xv lb≤x x≤ub (node y yv bal ls rs)
    | inr y≤x with insertWithin x xv y≤x x≤ub rs
... | stay rs′ = stay (node y yv bal ls rs′)
... | high rs′ with bal
... | ll = stay (node y yv ee ls rs′)
... | ee = high (node y yv rr ls rs′)
... | rr = rotˡ y yv ls rs′

-- infixr 5 _⟨_⟩∷_
-- data OrdList (lb : [∙]) : Type (k ℓ⊔ r) where
--   [] : OrdList lb
--   _⟨_⟩∷_ : (x : K) → lb [≤] [ x ] → OrdList [ x ] → OrdList lb

-- toList : Tree lb ub n → OrdList lb
-- toList tr = go tr []
--   where
--   go : Tree lb ub n → OrdList ub → OrdList lb
--   go (leaf x) [] = []
--   go {lb} {ub} (leaf p) (x ⟨ q ⟩∷ xs) = x ⟨ ≤-trans {lb} p q ⟩∷ xs
--   go (node x bal ls rs) xs = go ls (x ⟨ ≤-refl ⟩∷ go  rs xs)
