{-# OPTIONS --cubical --safe --postfix-projections #-}

module HITs.PropositionalTruncation.Properties where

open import HITs.PropositionalTruncation
open import Prelude

refute-trunc : ¬ A → ¬ ∥ A ∥
refute-trunc = rec isProp⊥

recompute : Dec A → ∥ A ∥ → A
recompute (yes p)  _  = p
recompute (no ¬p)  p  = ⊥-elim (rec isProp⊥ ¬p p)

open import HITs.PropositionalTruncation.Sugar

bij-iso : A ↔ B → ∥ A ∥ ⇔ ∥ B ∥
bij-iso A↔B .fun = _∥$∥_ (A↔B .fun)
bij-iso A↔B .inv = _∥$∥_ (A↔B .inv)
bij-iso A↔B .rightInv x = squash _ x
bij-iso A↔B .leftInv  x = squash _ x

bij-eq : A ↔ B → ∥ A ∥ ≡ ∥ B ∥
bij-eq = isoToPath ∘ bij-iso
