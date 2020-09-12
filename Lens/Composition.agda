{-# OPTIONS --cubical --safe #-}

module Lens.Composition where

open import Prelude
open import Lens.Definition
open import Lens.Operators

infixr 9 _⋯_
_⋯_ : Lens A B → Lens B C → Lens A C
(ab ⋯ bc) .into xs =
  let ab-xs = ab .into xs
      bc-ys = bc .into (ab-xs .get)
  in λ where .get → bc-ys .get
             .set → ab-xs .set ∘ bc-ys .set
(ab ⋯ bc) .get-set s v = cong _[ bc ] (ab .get-set s _) ; bc .get-set (ab .into s .get) v
(ab ⋯ bc) .set-get s = cong (s [ ab ]≔_) (bc .set-get (ab .into s .get)) ; ab .set-get s
(ab ⋯ bc) .set-set s v₁ v₂ = ab .set-set s _ _ ; cong (s [ ab ]≔_) (cong (_[ bc ]≔ v₂) (ab .get-set _ _) ; bc .set-set _ _ _)
