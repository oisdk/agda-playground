{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation.Sugar where

open import Cubical.HITs.PropositionalTruncation
open import Level

_=<<_ : ∀ {a} {A : Type a} {b} {B : ∥ A ∥ → Type b}
      → ((x : A) → ∥ B ∣ x ∣ ∥) → (xs : ∥ A ∥) → ∥ B xs ∥
_=<<_ = elimPropTrunc (λ _ → squash)

_>>=_ : ∀ {a} {A : Type a} {b} {B : Type b}
      → (xs : ∥ A ∥) → (A → ∥ B ∥) → ∥ B ∥
_>>=_ {a} {A} {b} {B} xs f = elimPropTrunc (λ _ → squash) f xs

_>>_ : ∥ A ∥ → ∥ B ∥ → ∥ B ∥
_ >> ys = ys

pure : A → ∥ A ∥
pure = ∣_∣

_<*>_ : ∥ (A → B) ∥ → ∥ A ∥ → ∥ B ∥
fs <*> xs = do
  f ← fs
  x ← xs
  ∣ f x ∣

infixr 1 _∥$∥_
_∥$∥_ : (A → B)→ ∥ A ∥ → ∥ B ∥
f ∥$∥ xs = recPropTrunc squash (λ x → ∣ f x ∣) xs
