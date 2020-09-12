{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Sum.Properties where

open import Prelude
open import Data.Sum
open import Data.Bool

sumAsSigma : A ⊎ B ≃ Σ[ x ⦂ Bool ] (if x then A else B)
sumAsSigma = isoToEquiv $
  iso
    (either (true ,_) (false ,_))
    (uncurry (bool inr inl))
    (λ { (false , _) → refl ; (true , _) → refl})
    (λ { (inl _) → refl ; (inr _) → refl})
