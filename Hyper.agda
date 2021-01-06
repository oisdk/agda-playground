{-# OPTIONS --cubical --safe #-}

module Hyper where

open import Prelude hiding (⊥)
open import Data.Empty.UniversePolymorphic
open import Data.List using (List; _∷_; [])
open import Data.Vec.Iterated
open import Data.Nat using (_*_; _+_)
open import Data.Nat.Properties using (Even; Odd)

private
  variable n m : ℕ

infixr 4 _#_↬_
_#_↬_ : ℕ → Type a → Type b → Type (a ℓ⊔ b)
zero  # A ↬ B = ⊥
suc n # A ↬ B = n # B ↬ A → B

module _ {a b} {A : Type a} {B : Type b} where
  yfld : Vec B n → 1 + n * 2 # List (A × B) ↬ (A → List (A × B))
  yfld =
    foldr
      (λ n → 1 + n * 2 # List (A × B) ↬ (A → List (A × B)))
      (λ y yk xk x → (x , y) ∷ xk yk)
      (λ ())

  xfld : Vec A n → (1 + n) * 2 # (A → List (A × B)) ↬ List (A × B)
  xfld =
    foldr
      (λ n → (1 + n) * 2 # (A → List (A × B)) ↬ List (A × B))
      (λ x xk yk → yk xk x)
      (λ _ → [])

  zip : Vec A n → Vec B n → List (A × B)
  zip xs ys = xfld xs (yfld ys)

module _ {A : Type a} {B : Type b} {C : Type c} where
  cata : Even n → (((C → A) → B) → C) → n # A ↬ B → C
  cata e phi = f e
    where
    f : Even n → n # A ↬ B → C
    f {n = suc (suc n)} e h = phi (λ g → h (g ∘ f e))

push : (A → B) -> n # A ↬ B -> 2 + n # A ↬ B
push {n = suc n} f q k = f (k q)

one : Odd n → n # A ↬ A
one {n = suc zero} o ()
one {n = suc (suc n)} o k = k (one o)
