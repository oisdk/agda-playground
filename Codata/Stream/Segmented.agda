open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Stream.Segmented
  {ℓ}
  (mon : TMAPOM ℓ)
  (𝓌𝒻 : WellFounded (TMAPOM._<_ mon))
  where

open TMAPOM mon

record Stream′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
  coinductive
  field
    head : A
    tail : ∀ {j} → j < i → Stream′ A j
open Stream′ public

private
  variable
    i j : 𝑆

Stream : Type a → Type (a ℓ⊔ ℓ)
Stream A = ∀ {i} → Stream′ A i

pure : A → Stream A
pure x .head = x
pure x .tail _ = pure x

map : (A → B) → Stream′ A i → Stream′ B i
map f xs .head = f (xs .head)
map f xs .tail j<i = map f (xs .tail j<i)

join : Stream′ (Stream′ A i) i → Stream′ A i
join xs .head = xs .head .head
join xs .tail j<i = join (map (λ ys → ys .tail j<i) (xs .tail j<i))

bind : Stream′ A i → (A → Stream′ B i) → Stream′ B i
bind xs f .head = f (xs .head) .head
bind xs f .tail j<i = bind (xs .tail j<i) (λ x → f x .tail j<i)
