{-# OPTIONS --without-K --safe #-}

module Data.Empty.Base where

open import Level

data ⊥ : Type where

infix 4.5 ¬_
¬_ : Type a → Type a
¬ A = A → ⊥

⊥-elim : ⊥ → A
⊥-elim ()
