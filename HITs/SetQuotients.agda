module HITs.SetQuotients where

open import Prelude
open import Cubical.HITs.SetQuotients
  using (_/_; [_]; eq/; squash/; elim; rec)
  public

-- data _/_ (A : Type a) (R : A → A → Type b) : Type (a ℓ⊔ b) where
--   ∣_∣ : A → A / R
--   quot : (x y : A) → R x y → ∣ x ∣ ≡ ∣ y ∣
--   trunc : isSet (A / R)

