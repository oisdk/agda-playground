{-# OPTIONS --cubical --safe --postfix-projections #-}

module Lens.Pair where

open import Prelude
open import Lens.Definition

⦅fst⦆ : Lens (A × B) A
⦅fst⦆ .into (x , y) = lens-part x (_, y)
⦅fst⦆ .get-set s v i = v
⦅fst⦆ .set-get s i = s
⦅fst⦆ .set-set s v₁ v₂ i = v₂ , s .snd

⦅snd⦆ : Lens (A × B) B
⦅snd⦆ .into (x , y) = lens-part y (x ,_)
⦅snd⦆ .get-set s v i = v
⦅snd⦆ .set-get s i = s
⦅snd⦆ .set-set s v₁ v₂ i = s .fst , v₂
