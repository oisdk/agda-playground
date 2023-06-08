{-# OPTIONS --cubical --no-termination-check --no-positivity-check #-}

module Hyper where

open import Prelude

infixr 0 _↬_
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive; constructor ⟪_⟫
  infixl 2 _·_
  field
    _·_ : B ↬ A → B
open _↬_

_∣_ : (B ↬ C) → (A ↬ B) → A ↬ C
(f ∣ g) · k = f · (g ∣ k)

_◃_ : (A → B) → A ↬ B → A ↬ B
(f ◃ h) · k = f (k · h)

[_] : (A → B) → A ↬ B
[ f ] = f ◃ [ f ]

module _ { A : Type a } where
  open import Path.Reasoning

  𝟘 : A ↬ A
  𝟘 · k = k · 𝟘

  -- 𝟘-id : 𝟘 ≡ [ id ]
  -- 𝟘-id i · k =
  --   begin[ i ]
  --     (k · 𝟘) ≡⟨ (λ j → k · 𝟘-id j) ⟩
  --     (k · [ id ]) ≡⟨⟩
  --     (id  (k · [ id ])) ≡⟨⟩
  --     ((id ◃ [ id ]) · k) ≡⟨⟩
  --     ([ id ] · k) ∎

-- 𝕀 : A ↬ A
-- 𝕀 · x = x · 𝕀

cata : (((C → A) → B) → C) → A ↬ B → C
cata ϕ h = ϕ λ k → h · ⟪ k ∘ cata ϕ ⟫

ana : (C → (C → A) → B) → C → A ↬ B
ana ψ r · x = ψ r λ y → x · ana ψ y

-- _◂_ : (B → C) → A ↬ B → A ↬ C
-- _◂_ f = ana λ h k → f (h · ⟪ k ⟫)

-- _▸_ : (B ↬ C) → (A → B) → A ↬ C
-- h ▸ f = ana (λ h k → h · ⟪ f ∘ k ⟫) h

