{-# OPTIONS --no-termination-check #-}

open import Prelude
open import Algebra

module Hyper.MonadComonadic {ℓ}  {𝑀 : Type ℓ → Type ℓ} {𝐺 : Type ℓ → Type ℓ}
  (mon   : Monad 𝑀)
  (comon : Comonad 𝐺) where


infixr 1 _↬_ _↬′_
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

k : B → A ↬ B
k x · _ = x

𝕀 : A ↬ A
𝕀 · x = extract x ⦇ 𝕀 ⦈

infixr 5 _◃_
_◃_ : (A → B) → A ↬ B → A ↬ B
f ◃ xs · k = f (extract k ⦇ xs ⦈)

△ : (A → B) → A ↬ B
△ f = f ◃ △ f

▽ : A ↬ B → 𝐺 A → B
▽ h x = h · cmap const x

cata : {C : Type ℓ} → ((𝐺 (𝑀 C → A) → B) → C) → A ↬ B → C
cata ϕ h = ϕ λ k → h · cmap (_∘ mmap (cata ϕ)) k

ana : {C : Type ℓ} → (C → 𝐺 (𝑀 C → A) → B) → C → A ↬ B
ana ψ r · k = ψ r (cmap (_∘ mmap (ana ψ)) k)

𝕄 : A ↬ A ↬ B → A ↬ B
𝕄 = cata λ where g · k → g k · k

𝕂 : A ↬ B ↬ A
𝕂 · x · y = extract x ⦇ 𝕂 ⦈
