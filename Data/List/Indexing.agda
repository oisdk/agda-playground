{-# OPTIONS --cubical --safe #-}

module Data.List.Indexing where

open import Data.List.Base
open import Data.Fin
open import Prelude

infixl 6 _!_
_!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) ! f0 = x
(x ∷ xs) ! fs i = xs ! i

tabulate : ∀ n → (Fin n → A) → List A
tabulate zero f = []
tabulate (suc n) f = f f0 ∷ tabulate n (f ∘ fs)
