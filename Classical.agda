{-# OPTIONS --cubical --safe #-}

module Classical where

open import Prelude
open import Relation.Nullary.Stable using (Stable) public
open import Relation.Nullary.Decidable.Properties using (Dec→Stable) public

Classical : Type a → Type a
Classical A = ¬ ¬ A

pure : A → Classical A
pure x k = k x

_>>=_ : Classical A → (A → Classical B) → Classical B
xs >>= f = λ k → xs λ x → f x k

_<*>_ : Classical (A → B) → Classical A → Classical B
fs <*> xs = λ k → fs λ f → xs λ x → k (f x)

lem : {A : Type a} → Classical (Dec A)
lem k = k (no (k ∘ yes))
