{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Relation.Binary

module Data.AVLTree {e} {E : Type e} {r} (totalOrder : TotalOrder E r) where

open import Relation.Binary.Construct.Bounded totalOrder
open import Data.Nat using (_+_)
open TotalOrder totalOrder using (_≤?_)

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

data Tree (lb ub : [∙]) : ℕ → Type (e ℓ⊔ r) where
  leaf : lb [≤] ub → Tree lb ub zero
  node : (x : E) → (bal : Bal n m l) → Tree lb [ x ] n → Tree [ x ] ub m → Tree lb ub (suc l)

private
  variable
    lb ub : [∙]

-- rotʳ : (y : E) →
--        (ls : Tree lb [ y ] (suc (suc m))) →
--        (rs : Tree [ y ] ub m) →
--        ∃[ u ] (Tree lb ub (if u then 3 + m else 2 + m))
-- rotʳ y (node x ll ls ls₁) rs = false , node x ee ls (node y ee ls₁ rs)
-- rotʳ y (node x ee ls ls₁) rs = true , node x rr ls (node y ll ls₁ rs)
-- rotʳ y (node x rr ls (node x₁ ll ls₁ ls₂)) rs = false , {!node !}
-- rotʳ y (node x rr ls (node x₁ ee ls₁ ls₂)) rs = false , {!!}
-- rotʳ y (node x rr ls (node x₁ rr ls₁ ls₂)) rs = false , {!!}
-- 
-- insertWithin : (x : E) →
--                (lb [≤] [ x ]) →
--                ([ x ] [≤] ub) →
--                (tr : Tree lb ub n) →
--                ∃[ u ] (Tree lb ub (if u then suc n else n))
-- insertWithin x lb≤x x≤ub (leaf x₁) = true , node x ee (leaf lb≤x) (leaf x≤ub)
-- insertWithin x lb≤x x≤ub (node y bal ls rs) with x ≤? y
-- insertWithin x lb≤x x≤ub (node y bal ls rs) | inl x≤y with insertWithin x lb≤x x≤y ls
-- insertWithin x lb≤x x≤ub (node y bal ls rs) | inl x≤y | false , ls′ = false , node y bal ls′ rs
-- insertWithin x lb≤x x≤ub (node y ll ls rs) | inl x≤y | true , ls′ = {!!} -- node y {!!} ls′ rs
-- insertWithin x lb≤x x≤ub (node y ee ls rs) | inl x≤y | true , ls′ = true , node y ll ls′ rs
-- insertWithin x lb≤x x≤ub (node y rr ls rs) | inl x≤y | true , ls′ = false , node y ee ls′ rs
-- insertWithin x lb≤x x≤ub (node y bal ls rs) | inr y≤x with insertWithin x y≤x x≤ub rs
-- insertWithin x lb≤x x≤ub (node y bal ls rs) | inr y≤x | false , rs′ = false , node y bal ls rs′
-- insertWithin x lb≤x x≤ub (node y ll ls rs) | inr y≤x | true , rs′ = false , node y ee ls rs′
-- insertWithin x lb≤x x≤ub (node y ee ls rs) | inr y≤x | true , rs′ = true , node y rr ls rs′
-- insertWithin x lb≤x x≤ub (node y rr ls rs) | inr y≤x | true , rs′ = true , node y {!!} ls rs′
