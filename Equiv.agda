{-# OPTIONS --cubical --safe #-}

module Equiv where

open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv
        ; equiv-proof
        ; _≃_)

open import Cubical.Foundations.Everything public using (ua)
open import Cubical.Foundations.Equiv public
  using (equivToIso; isPropIsEquiv)
  renaming (compEquiv to trans-≃; invEquiv to sym-≃)
