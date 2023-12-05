{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation where

open import Cubical.HITs.PropositionalTruncation
  using (rec; elim)
  renaming
    ( rec→Set to rec→set
    ; squash₁ to squash
    ; ∥_∥₁ to ∥_∥
    ; ∣_∣₁ to ∣_∣ 
    )
  public
