{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Sugar where

open import Prelude
open import Data.Maybe

infixl 4 _<*>_
_>>=_ : Maybe A → (A → Maybe B) → Maybe B
nothing  >>= f = nothing
just x   >>= f = f x

pure : A → Maybe A
pure = just

_<*>_ :  Maybe (A → B) →
         Maybe A →
         Maybe B
nothing   <*> xs       = nothing
just f    <*> nothing  = nothing
just f    <*> just x   = just (f x)

_>>_ : Maybe A → Maybe B → Maybe B
nothing >> _ = nothing
just _  >> y = y

guard : Bool → Maybe ⊤
guard false = nothing
guard true  = just tt

_<|>_ : Maybe A → Maybe A → Maybe A
nothing     <|> ys = ys
xs@(just _) <|> _ = xs
