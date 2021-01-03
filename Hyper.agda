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

Hyper : Type a → Type b → ℕ → Type (a ℓ⊔ b)
Hyper A B zero    = ⊥
Hyper A B (suc n) = Hyper B A n → B

module _ {a b} {A : Type a} {B : Type b} where
  xf : A → (Hyper (A → List (A × B)) (List (A × B)) n) → Hyper (A → List (A × B)) (List (A × B)) (2 + n)
  xf {n = suc n} x xk yk = yk xk x

  xb : Hyper (A → List (A × B)) (List (A × B)) 2
  xb _ = []

  yf : B → Hyper (List (A × B)) (A → (List (A × B))) n → Hyper (List (A × B)) (A → (List (A × B))) (2 + n)
  yf y yk xk x = (x , y) ∷ xk yk

  yb : Hyper (List (A × B)) (A → List (A × B)) 1
  yb ()

  yfld : Vec B n → Hyper (List (A × B)) (A → List (A × B)) (1 + n * 2)
  yfld = foldr (λ n → Hyper (List (A × B)) (A → List (A × B)) (1 + (n * 2))) yf yb

  xfld : Vec A n → Hyper (A → List (A × B)) (List (A × B)) ((1 + n) * 2)
  xfld = foldr (λ n → Hyper (A → List (A × B)) (List (A × B)) ((1 + n) * 2)) xf xb

  zip : Vec A n → Vec B n → List (A × B)
  zip xs ys = xfld xs (yfld ys)



module _ {A : Type a} {B : Type b} {C : Type c} where
  cata : Even n → (((C → A) → B) → C) → Hyper A B n → C
  cata e phi = f e
    where
    f : Even n → Hyper A B n → C
    f {n = suc (suc n)} e h = phi (λ g → h (g ∘ f e))

push : (A → B) -> Hyper A B n -> Hyper A B (2 + n)
push {n = suc n} f q k = f (k q)

one : Odd n → Hyper A A n
one {n = suc zero} o ()
one {n = suc (suc n)} o k = k (one o)
