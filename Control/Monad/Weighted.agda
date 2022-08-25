{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Level

module Control.Monad.Weighted {ℓ} {𝑆 : Type ℓ} (rng : Semiring 𝑆) where

open import Control.Monad.Weighted.Definition rng public
open import Control.Monad.Weighted.Union      rng using (_∪_) public
open import Control.Monad.Weighted.Cond       rng using (_⋊_) public
open import Control.Monad.Weighted.Monad      rng using (_>>=_; pure; _>>_; _<*>_) public

import Control.Monad.Weighted.Expect using (∫)

module Expect = Control.Monad.Weighted.Expect rng
