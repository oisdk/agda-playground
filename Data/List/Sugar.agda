{-# OPTIONS --cubical --safe #-}

module Data.List.Sugar where

open import Data.List.Base
open import Prelude

[_] : A → List A
[ x ] = x ∷ []

pure : A → List A
pure = [_]

_>>=_ : List A → (A → List B) → List B
_>>=_ = flip concatMap

_>>_ : List A → List B → List B
xs >> ys = xs >>= const ys

_<*>_ : List (A → B) → List A → List B
fs <*> xs = do
  f ← fs
  x ← xs
  [ f x ]

guard : Bool → List ⊤
guard false = []
guard true  = [ tt ]
