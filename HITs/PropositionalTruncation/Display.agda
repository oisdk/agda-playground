{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation.Display where

open import Prelude
open import Cubical.HITs.PropositionalTruncation

rec : isProp B → (A → B) → ∥ A ∥ → B
rec→set : isSet B → (f : A → B) → (∀ x y → f x ≡ f y) → ∥ A ∥ → B
rec = recPropTrunc
rec→set isSetB = recPropTrunc→Set isSetB
