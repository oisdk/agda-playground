{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude
open import Relation.Binary

module Data.RBTree {e} {E : Type e} {r₁ r₂} (totalOrder : TotalOrder E r₁ r₂) where

open import Relation.Binary.Construct.Bounded totalOrder

open TotalOrder totalOrder using (_≤?_)

data Colour : Type where
  red black : Colour

add-black : Colour → ℕ → ℕ
add-black red = λ n → n
add-black black = suc

private
  variable
    n : ℕ

data Tree (lb ub : [∙]) : ℕ → Type (e ℓ⊔ r₂) where
  leaf : lb [≤] ub → Tree lb ub n
  node : (x : E) → (c : Colour) → Tree lb [ x ] n → Tree [ x ] ub n → Tree lb ub (add-black c n)

private
  variable
    lb ub : [∙]

IsBlack : Tree lb ub n → Type
IsBlack (leaf x) = ⊤
IsBlack (node x red tr tr₁) = ⊥
IsBlack (node x black tr tr₁) = ⊤

Valid-rec : Tree lb ub n → Type
Valid-rec (leaf x) = ⊤
Valid-rec (node x red   xs ys) = IsBlack xs × IsBlack ys × Valid-rec xs × Valid-rec ys
Valid-rec (node x black xs ys) = Valid-rec xs × Valid-rec ys


Valid : Tree lb ub n → Type
Valid tr = IsBlack tr × Valid-rec tr

-- insertWithin : (x : E) →
--                (lb [≤] [ x ]) →
--                ([ x ] [≤] ub) →
--                (tr : Tree lb ub n) →
--                Valid-rec tr →
--                ∃[ c ] Σ (Tree lb ub (add-black c n)) Valid-rec
-- insertWithin x lb≤x x≤ub (leaf _) val = red , node x red (leaf lb≤x) (leaf x≤ub) , tt , tt , tt , tt
-- insertWithin x lb≤x x≤ub (node y c ls rs) val with x ≤? y
-- insertWithin x lb≤x x≤ub (node y red   ls rs) val | inl x≤y with insertWithin x lb≤x x≤y ls (fst (snd (snd val)))
-- insertWithin x lb≤x x≤ub (node y red   ls rs) val | inl x≤y | red    , ls′ , val′ = black , node y black ls′ rs , val′ , snd (snd (snd val))
-- insertWithin x lb≤x x≤ub (node y red   ls rs) val | inl x≤y | black  , ls′ , val′ = {!{!!} , node y {!!} ls′ rs , {!!}!}
-- insertWithin x lb≤x x≤ub (node y black ls rs) val | inl x≤y with insertWithin x lb≤x x≤y ls (fst val)
-- insertWithin x lb≤x x≤ub (node y black ls rs) val | inl x≤y | res = {!!}
-- insertWithin x lb≤x x≤ub (node y c ls rs) val | inr y≤x = {!!}

-- -- insertWithin x lb≤x x≤ub (node y ls rs) with x ≤? y
-- -- insertWithin x lb≤x x≤ub (node y ls rs) | inl x≤y = node y (insertWithin x lb≤x x≤y ls) rs
-- -- insertWithin x lb≤x x≤ub (node y ls rs) | inr y≤x = node y ls (insertWithin x y≤x x≤ub rs)
