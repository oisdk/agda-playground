{-# OPTIONS --cubical --safe --postfix-projections #-}

module Lens.Pair where

open import Prelude
open import Lens.Definition

⦅fst⦆ : Lens (A × B) A
⦅fst⦆ .fst (x , y) = lens-part x (_, y)
⦅fst⦆ .snd .get-set s v i = v
⦅fst⦆ .snd .set-get s i = s
⦅fst⦆ .snd .set-set s v₁ v₂ i = v₂ , s .snd

⦅snd⦆ : Lens (A × B) B
⦅snd⦆ .fst (x , y) = lens-part y (x ,_)
⦅snd⦆ .snd .get-set s v i = v
⦅snd⦆ .snd .set-get s i = s
⦅snd⦆ .snd .set-set s v₁ v₂ i = s .fst , v₂
