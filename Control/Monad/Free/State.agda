{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Free.State where

open import Control.Monad.Free
open import Prelude hiding (⊤)
open import Data.Unit.UniversePolymorphic
open import Algebra

data StateF {s} (S : Type s) (A : Type a)  : Type (s ℓ⊔ a) where
  getF : (S → A) → StateF S A
  putF : S → A → StateF S A

State : Type a → Type a → Type _
State S = Free (StateF S)

get : State A A
get = lift (getF id)

put : A → State A ⊤
put x = lift (putF x _)

module _ {s} {S : Type s} where
  functorState : Functor s s
  functorState .Functor.𝐹 = StateF S
  functorState .Functor.map f (getF x) = getF (f ∘ x)
  functorState .Functor.map f (putF s x) = putF s (f x)
  functorState .Functor.map-id i (getF x) = getF x
  functorState .Functor.map-id i (putF x x₁) = putF x x₁
  functorState .Functor.map-comp f g i (getF x) = getF (f ∘ g ∘ x)
  functorState .Functor.map-comp f g i (putF x x₁) = putF x (f (g x₁))

private variable
  s : Level
  S : Type s

runState : State S A → S → A × S
runState = cata functorState {!!} _,_ λ { (getF k) s → k s s ; (putF s₂ k) s₁ → k s₂ }

open import Data.Nat using (_∸_)

example : State ℕ ℕ
example = do
  x ← get
  put (suc x)
  put x
  return (x ∸ 1)

res : ℕ × ℕ
res = runState example 5
