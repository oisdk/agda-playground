open import Algebra

module Control.Monad.Weighted.Depth {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels
open import Prelude

open import Control.Monad.Weighted rng

mutual
  record Deep (A : Type a) : Type (ℓ ℓ⊔ a) where
    coinductive
    constructor _◀_
    field
      root : A
      rest : Depth A

  data Depth (A : Type a) : Type (ℓ ℓ⊔ a) where
    ⟪_⟫ : Weighted (Deep A) → Depth A
    flat : (xs : Weighted (A × Weighted (Deep A))) → ⟪ xs >>= (λ { (x , xs) → 1# ◃ (x ◀ ⟪ [] ⟫) ∷ xs }) ⟫ ≡ ⟪ xs >>= (λ { (x , xs) → pure (x ◀ ⟪ xs ⟫) }) ⟫

    ⟪trunc⟫ : isSet (Depth A)
    
