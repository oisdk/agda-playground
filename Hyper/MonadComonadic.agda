{-# OPTIONS --no-termination-check #-}

open import Prelude
open import Algebra

module Hyper.MonadComonadic {ℓ}  {𝑀 : Type ℓ → Type ℓ} {𝐺 : Type ℓ → Type ℓ}
  (mon   : Monad 𝑀)
  (comon : Comonad 𝐺) where


_↬′_ : Type ℓ → Type ℓ → Type ℓ
record _↬_ (A : Type ℓ) (B : Type ℓ) : Type ℓ

{-# NO_POSITIVITY_CHECK #-}
record _↬_ A B where
  inductive; constructor hyp
  infixl 4 _·_
  field _·_ : 𝐺 (B ↬′ A) → B
A ↬′ B = 𝑀 (B ↬ A) → B

open _↬_

open Monad mon
open Comonad comon

pure : A → 𝑀 A
pure = return

_<*>_ : 𝑀 (A → B) → 𝑀 A → 𝑀 B
fs <*> xs = do
  f ← fs
  x ← xs
  pure (f x)

infixr 9 _⊙_ _⊙′_ _⊙″_
mutual
  _⊙″_ : (B ↬′ C) → 𝑀 (A ↬ B) → (A ↬′ C)
  (f ⊙″ g) k = f ⦇ g ⊙ k ⦈

  _⊙′_ : B ↬ C → 𝐺 (A ↬′ B) → (A ↬′ C)
  (f ⊙′ g) k = f · cmap (_⊙″ k) g

  _⊙_ : B ↬ C → A ↬ B → A ↬ C
  f ⊙ g · k = f · extend (g ⊙′_) k
