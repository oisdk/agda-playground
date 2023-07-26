{-# OPTIONS --cubical --safe #-}

module Data.Vec where

open import Prelude

private
  variable
    n m : ℕ

infixr 5 _∷_
data Vec (A : Type a) : ℕ → Type a where
  [] : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

head : Vec A (suc n) → A
head (x ∷ _) = x

foldr : (A → B → B) → B → Vec A n → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

vmap : (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

isProp-[] : isProp (Vec A zero)
isProp-[] [] [] = refl
