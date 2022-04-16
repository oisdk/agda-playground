{-# OPTIONS --no-termination-check #-}

open import Algebra
open import Prelude

module Hyper.Monadic {m} {𝑀 : Type m → Type m} (mon : Monad 𝑀) where

open Monad mon

_↬′_ : Type m → Type m → Type m
record _↬_ (A : Type m) (B : Type m) : Type m

A ↬′ B = 𝑀 (B ↬ A) → B

pure : A → 𝑀 A
pure = return

_<*>_ : 𝑀 (A → B) → 𝑀 A → 𝑀 B
fs <*> xs = do
  f ← fs
  x ← xs
  pure (f x)

{-# NO_POSITIVITY_CHECK #-}
record _↬_ A B where
  inductive; constructor hyp
  infixl 4 _·_
  field _·_ : B ↬′ A → B
open _↬_ public

infixr 9 _⊙_ _⊙′_ _⊙″_
mutual
  _⊙″_ : B ↬′ C → 𝑀 (A ↬ B) → A ↬′ C
  (f ⊙″ g) k = f ⦇ g ⊙ k ⦈

  _⊙′_ : B ↬ C → A ↬′ B → A ↬′ C
  (f ⊙′ g) k = f · g ⊙″ k

  _⊙_ : B ↬ C → A ↬ B → A ↬ C
  f ⊙ g · k = f · g ⊙′ k

_◃_ : (A → B) → A ↬ B → A ↬ B
(f ◃ h) · k = f (k (return h))

k : A → B ↬ A
k x · _ = x

△ : (A → B) → A ↬ B
△ f · k = f (k (return (△ f)))

𝕀 : A ↬ A
𝕀 · x = x (return 𝕀)

▽ : A ↬ B → A → B
▽ h x = h · λ _ → x


-- run : A ↬ A → A
-- run x = x · λ k → {!k !}
