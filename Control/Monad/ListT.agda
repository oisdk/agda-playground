{-# OPTIONS --cubical --no-positivity-check --no-termination-check #-}

open import Prelude
open import Algebra
open import Relation.Binary

module Control.Monad.ListT
  {ℓ}
  (mon : Monad ℓ ℓ)
  where

open Monad mon

infixr 5 _∷_
mutual
  List : Type ℓ → Type ℓ
  List A = 𝐹 (Cons A)

  data Cons (A : Type ℓ) : Type ℓ where
    [] : Cons A
    _∷_ : A → List A → Cons A

lmap : (A → B) → List A → List B
lmap f = map λ { [] → [] ; (x ∷ xs) → f x ∷ lmap f xs}

lpure : A → List A
lpure x = pure (x ∷ pure [])

infixr 5 _++_

_++_ : List A → List A → List A
xs ++ ys = xs >>= λ { [] → ys ; (x ∷ xs) → pure (x ∷ (xs ++ ys)) }

lbind : List A → (A → List B) → List B
lbind xs f = xs >>= λ { [] → pure [] ; (x ∷ xs) → f x ++ lbind xs f}
