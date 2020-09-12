{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation where

open import Cubical.HITs.PropositionalTruncation
  using (squash; ∥_∥; ∣_∣)
  renaming (recPropTrunc to rec; recPropTrunc→Set to rec→set)
  public
