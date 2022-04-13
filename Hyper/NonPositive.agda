{-# OPTIONS --no-termination-check #-}

module Hyper.NonPositive where

open import Prelude

infixr 2 _↬_
{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor hyp; inductive
  infixl 4 _·_
  field _·_ : (B ↬ A) → B
open _↬_ public

_⊙_ : B ↬ C → A ↬ B → A ↬ C
(f ⊙ g) · k = f · (g ⊙ k)

𝕀 : A ↬ A
𝕀 · k = k · 𝕀

𝕂 : A ↬ B ↬ A
𝕂 · x · y = x · 𝕂

infixr 4 _◃_
_◃_ : (A → B) → A ↬ B → A ↬ B
(f ◃ h) · k = f (k · h)

infixl 4 _▹_
_▹_ : A ↬ B → (B → A) → A ↬ B
h ▹ f · k = h · (f ◃ k)

_◂_▸_ : ∀ {a′ b′} {A′ : Type a′} {B′ : Type b′} → (B → B′) → A ↬ B → (A′ → A) → A′ ↬ B′
(f ◂ h ▸ g) · k = f (h · (g ◂ k ▸ f))

mutual
  infixr 4 _◂_
  _◂_ : (B → C) → A ↬ B → A ↬ C
  (f ◂ h) · k = f (h · (k ▸ f))

  infixl 4 _▸_
  _▸_ : (B ↬ C) → (A → B) → A ↬ C
  h ▸ f · k = h · (f ◂ k)

H : (A → B) → A ↬ B
H f · k = f (k · H f)

k : A → B ↬ A
k x · _ = x

ana : (A → (A → B) → C) → A → B ↬ C
ana ψ x · y = ψ x (λ z → y · ana ψ z)

cata : (((A → B) → C) → A) → B ↬ C → A
cata ϕ h = ϕ λ g → h · hyp (g ∘ cata ϕ)

unroll : A ↬ B → (A ↬ B → A) → B
unroll x f = x · hyp f

roll : ((A ↬ B → A) → B) → A ↬ B
roll f · k = f (k ·_)

𝕊 : A ↬ (B → C) → A ↬ B → A ↬ C
𝕊 = curry (ana λ { (i , j) fga → (i · hyp (fga ∘ (_, j))) (j · hyp (fga ∘ (i ,_))) })

𝕄 : A ↬ A ↬ B → A ↬ B
𝕄 h · k = h · hyp (λ x → k · 𝕄 x) · k
