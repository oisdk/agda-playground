{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary

module Data.AVLTree {e} {E : Type e} {r} (totalOrder : TotalOrder E r) where

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
    Val : E → Type v

data Tree {v} (Val : E → Type v) (lb ub : [∙]) : ℕ → Type (e ℓ⊔ r ℓ⊔ v) where
  leaf : lb [≤] ub → Tree Val lb ub zero
  node : (key : E) (val : Val key) (bal : Bal n m l) → Tree Val lb [ key ] n → Tree Val [ key ] ub m → Tree Val lb ub (suc l)

private
  variable
    lb ub : [∙]

rotʳ : (x : E) →
       (vl : Val x) →
       (ls : Tree Val lb [ x ] (2 + n)) →
       (rs : Tree Val [ x ] ub n) →
       ∃[ u ] (Tree Val lb ub (if u then 3 + n else 2 + n))
rotʳ y vl (node x v ll ls ls₁) rs = false , node x v ee ls (node y vl ee ls₁ rs)
rotʳ y vl (node x v ee ls ls₁) rs = true , node x v rr ls (node y vl ll ls₁ rs)
rotʳ x xv (node y yv rr a (node z zv bl b c)) d = false , node z zv ee (node y yv (balr bl) a b) (node x xv (ball bl) c d)


rotˡ : (x : E) → (xv : Val x) →
       (ls : Tree Val lb [ x ] n) →
       (rs : Tree Val [ x ] ub (2 + n)) →
       ∃[ u ] (Tree Val lb ub (if u then 3 + n else 2 + n))
rotˡ x xv ls (node y yv ee rs rs₁) = true , node y yv ll (node x xv rr ls rs) rs₁
rotˡ x xv ls (node y yv rr rs rs₁) = false , node y yv ee (node x xv ee ls rs) rs₁
rotˡ y yv a (node x xv ll (node z zv bl b c) d) = false , node z zv ee (node y yv (balr bl) a b) (node x xv (ball bl) c d)

insertWithin : (x : E) → Val x →
               (lb [≤] [ x ]) →
               ([ x ] [≤] ub) →
               (tr : Tree Val lb ub n) →
               ∃[ u ] (Tree Val lb ub (if u then suc n else n))
insertWithin x xv lb≤x x≤ub (leaf x₁) = true , node x xv ee (leaf lb≤x) (leaf x≤ub)
insertWithin x xv lb≤x x≤ub (node y yv bal ls rs) with x ≤? y
insertWithin x xv lb≤x x≤ub (node y yv bal ls rs) | inl x≤y with insertWithin x xv lb≤x x≤y ls
insertWithin x xv lb≤x x≤ub (node y yv bal ls rs) | inl x≤y | false , ls′ = false , node y yv bal ls′ rs
insertWithin x xv lb≤x x≤ub (node y yv ll ls rs) | inl x≤y | true , ls′ = rotʳ y yv ls′ rs
insertWithin x xv lb≤x x≤ub (node y yv ee ls rs) | inl x≤y | true , ls′ = true , node y yv ll ls′ rs
insertWithin x xv lb≤x x≤ub (node y yv rr ls rs) | inl x≤y | true , ls′ = false , node y yv ee ls′ rs
insertWithin x xv lb≤x x≤ub (node y yv bal ls rs) | inr y≤x with insertWithin x xv y≤x x≤ub rs
insertWithin x xv lb≤x x≤ub (node y yv bal ls rs) | inr y≤x | false , rs′ = false , node y yv bal ls rs′
insertWithin x xv lb≤x x≤ub (node y yv ll ls rs) | inr y≤x | true , rs′ = false , node y yv ee ls rs′
insertWithin x xv lb≤x x≤ub (node y yv ee ls rs) | inr y≤x | true , rs′ = true , node y yv rr ls rs′
insertWithin x xv lb≤x x≤ub (node y yv rr ls rs) | inr y≤x | true , rs′ = rotˡ y yv ls rs′

-- infixr 5 _⟨_⟩∷_
-- data OrdList (lb : [∙]) : Type (e ℓ⊔ r) where
--   [] : OrdList lb
--   _⟨_⟩∷_ : (x : E) → lb [≤] [ x ] → OrdList [ x ] → OrdList lb

-- toList : Tree lb ub n → OrdList lb
-- toList tr = go tr []
--   where
--   go : Tree lb ub n → OrdList ub → OrdList lb
--   go (leaf x) [] = []
--   go {lb} {ub} (leaf p) (x ⟨ q ⟩∷ xs) = x ⟨ ≤-trans {lb} p q ⟩∷ xs
--   go (node x bal ls rs) xs = go ls (x ⟨ ≤-refl ⟩∷ go  rs xs)
