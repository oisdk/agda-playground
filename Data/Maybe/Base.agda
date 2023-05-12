{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Base where

open import Level
open import Agda.Builtin.Maybe public

maybe : {B : Maybe A → Type b} → B nothing → ((x : A) → B (just x)) → (x : Maybe A) → B x
maybe b f nothing = b
maybe b f (just x) = f x

mapMaybe : (A → B) → Maybe A → Maybe B
mapMaybe f nothing  = nothing
mapMaybe f (just x) = just (f x)

fromMaybe : A → Maybe A → A
fromMaybe x = maybe x (λ x → x)

infixr 2 _|?_
_|?_ : Maybe A → A → A
_|?_ = λ x y → fromMaybe y x
