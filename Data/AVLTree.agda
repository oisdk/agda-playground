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

data Tree (lb ub : [∙]) : ℕ → Type (e ℓ⊔ r) where
  leaf : lb [≤] ub → Tree lb ub zero
  node : (x : E) → (bal : Bal n m l) → Tree lb [ x ] n → Tree [ x ] ub m → Tree lb ub (suc l)

private
  variable
    lb ub : [∙]

rotʳ : (x : E) →
       (ls : Tree lb [ x ] (2 + n)) →
       (rs : Tree [ x ] ub n) →
       ∃[ u ] (Tree lb ub (if u then 3 + n else 2 + n))
rotʳ y (node x ll ls ls₁) rs = false , node x ee ls (node y ee ls₁ rs)
rotʳ y (node x ee ls ls₁) rs = true , node x rr ls (node y ll ls₁ rs)
rotʳ x (node y rr a (node z bl b c)) d = false , node z ee (node y (balr bl) a b) (node x (ball bl) c d)


rotˡ : (x : E) →
       (ls : Tree lb [ x ] n) →
       (rs : Tree [ x ] ub (2 + n)) →
       ∃[ u ] (Tree lb ub (if u then 3 + n else 2 + n))
rotˡ x ls (node x₁ ee rs rs₁) = true , node x₁ ll (node x rr ls rs) rs₁
rotˡ x ls (node x₁ rr rs rs₁) = false , node x₁ ee (node x ee ls rs) rs₁
rotˡ y a (node x ll (node z bl b c) d) = false , node z ee (node y (balr bl) a b) (node x (ball bl) c d)

insertWithin : (x : E) →
               (lb [≤] [ x ]) →
               ([ x ] [≤] ub) →
               (tr : Tree lb ub n) →
               ∃[ u ] (Tree lb ub (if u then suc n else n))
insertWithin x lb≤x x≤ub (leaf x₁) = true , node x ee (leaf lb≤x) (leaf x≤ub)
insertWithin x lb≤x x≤ub (node y bal ls rs) with x ≤? y
insertWithin x lb≤x x≤ub (node y bal ls rs) | inl x≤y with insertWithin x lb≤x x≤y ls
insertWithin x lb≤x x≤ub (node y bal ls rs) | inl x≤y | false , ls′ = false , node y bal ls′ rs
insertWithin x lb≤x x≤ub (node y ll ls rs) | inl x≤y | true , ls′ = rotʳ y ls′ rs
insertWithin x lb≤x x≤ub (node y ee ls rs) | inl x≤y | true , ls′ = true , node y ll ls′ rs
insertWithin x lb≤x x≤ub (node y rr ls rs) | inl x≤y | true , ls′ = false , node y ee ls′ rs
insertWithin x lb≤x x≤ub (node y bal ls rs) | inr y≤x with insertWithin x y≤x x≤ub rs
insertWithin x lb≤x x≤ub (node y bal ls rs) | inr y≤x | false , rs′ = false , node y bal ls rs′
insertWithin x lb≤x x≤ub (node y ll ls rs) | inr y≤x | true , rs′ = false , node y ee ls rs′
insertWithin x lb≤x x≤ub (node y ee ls rs) | inr y≤x | true , rs′ = true , node y rr ls rs′
insertWithin x lb≤x x≤ub (node y rr ls rs) | inr y≤x | true , rs′ = rotˡ y ls rs′

infixr 5 _⟨_⟩∷_
data OrdList (lb : [∙]) : Type (e ℓ⊔ r) where
  [] : OrdList lb
  _⟨_⟩∷_ : (x : E) → lb [≤] [ x ] → OrdList [ x ] → OrdList lb

toList : Tree lb ub n → OrdList lb
toList tr = go tr []
  where
  go : Tree lb ub n → OrdList ub → OrdList lb
  go (leaf x) [] = []
  go {lb} {ub} (leaf p) (x ⟨ q ⟩∷ xs) = x ⟨ ≤-trans {lb} p q ⟩∷ xs
  go (node x bal ls rs) xs = go ls (x ⟨ ≤-refl ⟩∷ go  rs xs)
