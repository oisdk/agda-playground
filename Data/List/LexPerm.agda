open import Prelude
open import Relation.Binary

module Data.List.LexPerm
  {ℓ ℓ₁ ℓ₂}
  {E : Type ℓ}
  (rel : TotalOrder E ℓ₁ ℓ₂)
  where

open TotalOrder rel

open import Data.List

open import Data.Fin
open import Data.List.Syntax

_!!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) !! fs i = xs !! i
(x ∷ xs) !! f0 = x

nextLexPerm : List E → Maybe (List E)
nextLexPerm xs = foldr f n xs f0
  where
  PC : Type _
  PC = (s : Fin 4) →
    [ Maybe (List E)
    , (E → Maybe (List E))
    , (List E → E → E → List E)
    , (List E → List E)
    ] !! s

  n : PC
  n f0        = nothing
  n f1 _      = nothing
  n f2 ys i j = j ∷ i ∷ ys
  n f3 ys     = ys

  f : E → PC → PC
  f x xs f0     = xs f1 x
  f y xs f1 x with xs f1 y
  ... | just ys = just (x ∷ ys)
  ... | nothing with x <? y
  ... | yes _   = just (xs f2 [] x y)
  ... | no  _   = nothing
  f k xs f2 ys i j with i <? k 
  ... | yes _   = xs f2 (j ∷ ys) i k
  ... | no  _   = xs f3 (k ∷ ys)
  f k xs f3 ys  = xs f3 (k ∷ ys)
