{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Free.Quotiented.Containers where

open import Prelude
open import Container
open import HITs.SetQuotients

data Syntax (F : Container ℓzero ℓzero) (A : Type) : Type where
  return : A → Syntax F A
  op : ⟦ F ⟧ (Syntax F A) → Syntax F A

Free : (F : Container ℓzero ℓzero) (_~_ : ∀ {X} → Syntax F X → Syntax F X → Type) (A : Type)  → Type
Free F _~_ A = Syntax F A / _~_

private
  variable
    F G : Container ℓzero ℓzero
    _~_ : ∀ {X} → Syntax F X → Syntax F X → Type

smap : (A → B) → Syntax F A → Syntax F B
smap f (return x) = return (f x)
smap f (op x) = op (cmap (smap f) x)

module _ {_~_ : ∀ {X} → Syntax F X → Syntax F X → Type} where
  fmap : (A → B) → Free F _~_ A → Free F _~_ B
  fmap f = rec squash/ ([_] ∘ smap f) {!!}

  module _ {A : Type} where
    join : Free F _~_ (Free F _~_ A) → Free F _~_ A
    join = rec squash/ ϕ {!!}
      where
        ϕ : Syntax F (Free F _~_ A) → Free F _~_ A
        ϕ (return x) = x
        ϕ (op x)     = {!!}
