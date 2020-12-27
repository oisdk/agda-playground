{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Sign where

open import Prelude

data Signed {a} (A : Type a) : Type a where
  ⁻_ : A → Signed A
  ±0 : Signed A
  ⁺_ : A → Signed A

unsign : (A → B) → B → (A → B) → Signed A → B
unsign f g h (⁻ x) = f x
unsign f g h ±0 = g
unsign f g h (⁺ x) = h x
