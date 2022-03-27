{-# OPTIONS --cubical --guardedness #-}

module HyperPositive where

open import Prelude

infixr 4 _↬_
{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive; constructor hyp
  field invoke : ((A ↬ B) → A) → B
open _↬_

open import Data.List using (List; _∷_; []; foldr)

module _ {a b} {A : Type a} {B : Type b} where
  XT = List (A × B) ↬ (A → List (A × B)) → List (A × B)
  YT = List (A × B) ↬ (A → List (A × B))

  yfld : List B → YT
  yfld = foldr f n
    where
    f : B → YT → YT
    f y yk .invoke xk x = (x , y) ∷ xk yk

    n : YT
    n .invoke _ _ = []

  xfld : List A → XT
  xfld = foldr f n
    where
    f : A → XT → XT
    f x xk yk = yk .invoke xk x

    n : XT
    n _ = []

  zip : List A → List B → List (A × B)
  zip xs ys = xfld xs (yfld ys)

open import Data.List using (_⋯_)
open import Data.List.Syntax

_ : zip (1 ⋯ 5) (11 ⋯ 15) ≡ [ 5 ][ (1 , 11) , (2 , 12) , (3 , 13) , (4 , 14) , (5 , 15) ]
_ = refl

open import Data.List

record Tree (A : Type a) : Type a where
  inductive; pattern; constructor _&_
  field
    root : A
    children : List (Tree A)
open Tree

{-# NON_TERMINATING #-}
loop : (A ↬ A) → A
loop k = k .invoke loop

{-# TERMINATING #-}
bfe : Tree A → List A
bfe t = f t d .invoke loop zero
  where
  f : Tree A → ((ℕ → List A) ↬ (ℕ → List A)) → ((ℕ → List A) ↬ (ℕ → List A))
  f (x & xs) fw .invoke bw n = x ∷ fw .invoke (bw ∘ flip (foldr f) xs) (suc n)

  d : ((ℕ → List A) ↬ (ℕ → List A))
  d .invoke k zero    = []
  d .invoke k (suc n) = k d n 
