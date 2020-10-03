{-# OPTIONS --cubical --safe #-}

module Control.Monad.State where

open import Prelude

record StatePair {s a} (S : Type s) (A : Type a) : Type (a ℓ⊔ s) where
  constructor state-pair
  field
    value : A
    state : S
open StatePair public

State : ∀ {s a} → Type s → Type a → Type (s ℓ⊔ a)
State S A = S → StatePair S A

private
  variable
    s : Level
    S : Type s

pure : A → State S A
pure = state-pair

_<*>_ : State S (A → B) → State S A → State S B
(fs <*> xs) s =
  let state-pair f s′ = fs s
      state-pair x s″ = xs s′
  in state-pair (f x) s″

_>>=_ : State S A → (A → State S B) → State S B
(xs >>= f) s = let state-pair x s′ = xs s in f x s′

get : State S S
value (get s) = s
state (get s) = s

modify : (S → S) → State S ⊤
value (modify f s) = tt
state (modify f s) = f s

put : S → State S ⊤
value (put s _) = tt
state (put s _) = s
