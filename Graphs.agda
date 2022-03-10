module Graphs where

open import Prelude
open import Data.List

GraphOf : Type a → Type a
GraphOf A = A → List A
