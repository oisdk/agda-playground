{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation where

open import Cubical.HITs.PropositionalTruncation
  using (squash; ∥_∥; ∣_∣; rec)
  renaming (rec→Set to rec→set)
  public
