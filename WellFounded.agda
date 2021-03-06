{-# OPTIONS --cubical --safe #-}

module WellFounded where

open import Level

data Acc {a r} {A : Type a} (R : A → A → Type r) (x : A) : Type (a ℓ⊔ r) where
  acc : (∀ y → R y x → Acc R y) → Acc R x

-- record Acc {a r} {A : Type a} (R : A → A → Type r) (x : A) : Type (a ℓ⊔ r) where
--   inductive
--   constructor acc
--   field step : ∀ y → R y x → Acc R y
-- open Acc public


WellFounded : ∀ {r} → (A → A → Type r) → Type _
WellFounded R = ∀ x → Acc R x

open import HLevels
open import Path

isPropAcc : ∀ {r} {R : A → A → Type r} {x : A} → isProp (Acc R x)
isPropAcc (acc x) (acc y) = cong acc (funExt λ n → funExt λ p → isPropAcc (x n p) (y n p))
