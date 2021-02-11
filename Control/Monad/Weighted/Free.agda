{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Weighted.Free {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Union rng
open import Control.Monad.Weighted.Cond rng
