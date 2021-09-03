{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Dyck.Payload where

open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions
--------------------------------------------------------------------------------

infixl 6 _*_
data Tree (A : Type a) : Type a where
  [_] : A → Tree A
  _*_ : Tree A → Tree A → Tree A

--------------------------------------------------------------------------------
-- Dyckrams: definition and associated functions
--------------------------------------------------------------------------------

infixr 5 ⟨_!_ ⟩_
data Dyck (A : Type a) : ℕ → Type a where
  ⟩⋆   : Dyck A 1
  ⟨_!_ : A → Dyck A (1 + n) → Dyck A n
  ⟩_   : Dyck A (1 + n) → Dyck A (2 + n)

--------------------------------------------------------------------------------
-- Conversion from a Dyck to a Tree
--------------------------------------------------------------------------------

dyck→tree⊙ : Dyck A n → Vec (Tree A) n → Tree A
dyck→tree⊙ ⟩⋆         (v ∷ [])       = v
dyck→tree⊙ (⟨ v ! is) st             = dyck→tree⊙ is ([ v ] ∷ st)
dyck→tree⊙ (⟩     is) (t₁ ∷ t₂ ∷ st) = dyck→tree⊙ is (t₂ * t₁ ∷ st)

dyck→tree : Dyck A zero → Tree A
dyck→tree ds = dyck→tree⊙ ds []

--------------------------------------------------------------------------------
-- Conversion from a Tree to a Dyck
--------------------------------------------------------------------------------

tree→dyck⊙ : Tree A → Dyck A (suc n) → Dyck A n
tree→dyck⊙ [ x ]     = ⟨ x !_
tree→dyck⊙ (xs * ys) = tree→dyck⊙ xs ∘ tree→dyck⊙ ys ∘ ⟩_

tree→dyck : Tree A → Dyck A zero
tree→dyck tr = tree→dyck⊙ tr ⟩⋆

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

tree→dyck→tree⊙ :  {is : Dyck A (1 + n)} {st : Vec (Tree A) n} (e : Tree A) →
  dyck→tree⊙ (tree→dyck⊙ e is) st ≡ dyck→tree⊙ is (e ∷ st)
tree→dyck→tree⊙ [ x ]     = refl
tree→dyck→tree⊙ (xs * ys) = tree→dyck→tree⊙ xs ; tree→dyck→tree⊙ ys

dyck→tree→dyck⊙ :  {st : Vec (Tree A) n} (is : Dyck A n) →
 tree→dyck (dyck→tree⊙ is st) ≡ foldlN (Dyck A) tree→dyck⊙ is st
dyck→tree→dyck⊙  ⟩⋆        = refl
dyck→tree→dyck⊙ (⟨ v ! is) = dyck→tree→dyck⊙ is
dyck→tree→dyck⊙ (⟩     is) = dyck→tree→dyck⊙ is

dyck-iso : Dyck A zero ⇔ Tree A
dyck-iso .fun = dyck→tree
dyck-iso .inv = tree→dyck
dyck-iso .rightInv = tree→dyck→tree⊙
dyck-iso .leftInv  = dyck→tree→dyck⊙

_ : tree→dyck (([ 1 ] * ([ 2 ] * [ 3 ])) * [ 4 ]) ≡ ⟨ 1 ! ⟨ 2 ! ⟨ 3 ! ⟩ ⟩ ⟨ 4 ! ⟩ ⟩⋆
_ = refl
