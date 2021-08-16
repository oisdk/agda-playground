{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Stream.Segmented
  {ℓ}
  (mon : CTMAPOM ℓ)
  where

open CTMAPOM mon

module Approach1 (𝓌𝒻 : WellFounded (CTMAPOM._<_ mon)) where
  record Stream′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
    inductive
    field
      head : A
      size : 𝑆
      tail : (p : size ≤ i) → Maybe (Stream′ A (fst p))
  open Stream′ public

  private
    variable
      i j : 𝑆

  Stream : Type a → Type (a ℓ⊔ ℓ)
  Stream A = ∀ {i} → Stream′ A i

  pure : A → Stream A
  pure x .head = x
  pure x .size = ε
  pure x .tail _ = nothing

  module _ (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
    repeat′ : Acc _<_ i → Stream′ A i
    repeat′ a .head = x
    repeat′ a .size = s
    repeat′ (acc wf) .tail (k , p) = just (repeat′ (wf _ (≤⇒≢ε⇒< k _ (s , p ; comm s k) s≢ε)))

    repeat : Stream A
    repeat = repeat′ (𝓌𝒻 _)

  map : (A → B) → Stream′ A i → Stream′ B i
  map f xs .head = f (xs .head)
  map f xs .size = xs .size
  map f xs .tail p = case xs .tail p of λ { nothing → nothing ; (just xs′) → just (map f xs′) }

  open import Data.List using (List; _∷_; [])

  take′ : ∀ i → Stream′ A i → List A
  take′ i xs with size xs ≤? i
  take′ i xs | no  _   = []
  take′ i xs | yes s≤i with tail xs s≤i
  take′ i xs | yes s≤i | nothing = []
  take′ i xs | yes s≤i | just xs′ = head xs′ ∷ take′ _ xs′

  take : 𝑆 → Stream A → List A
  take x xs = head (xs {i = x}) ∷ take′ x xs

module Approach2 (𝓌𝒻 : WellFounded (CTMAPOM._≺_ mon)) where
  data Wrap (A : Type a) : Type a where
    ◃_ : A → Wrap A

  record Stream′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
    inductive
    field
      weight : 𝑆
      uncons : (w<i : weight ≺ i) → A × Wrap (Stream′ A (fst (fst w<i)))
  open Stream′ public

  private
    variable
      i j : 𝑆

  Stream : Type a → Type (a ℓ⊔ ℓ)
  Stream A = ∀ {i} → Stream′ A i

  empty : Stream A
  empty {i = i} .weight = i
  empty {i = i} .uncons i<i = ⊥-elim (≺⇒< i i i<i ≤-refl)

  pure : A → Stream A
  pure x .weight = ε
  pure x {i} .uncons ε<i .fst = x
  pure x {i} .uncons ε<i .snd = ◃ empty

  module _ (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
    repeat′ : Acc _≺_ i → Stream′ A i
    repeat′ a .weight = s
    repeat′ a .uncons s<i .fst = x
    repeat′ {i = i} (acc wf) .uncons ((k , i≡s∙k) , k≢ε) .snd = ◃ repeat′ (wf k ((s , i≡s∙k ; comm s k) , s≢ε))

    repeat : Stream A
    repeat = repeat′ (𝓌𝒻 _)

  map : (A → B) → Stream′ A i → Stream′ B i
  map f xs .weight = xs .weight
  map f xs .uncons w<i with uncons xs w<i
  map f xs .uncons w<i | y , ◃ ys = f y , ◃ map f ys

  open import Data.List using (List; _∷_; [])

  take′ : ∀ i → Stream′ A i → List A
  take′ i xs with weight xs <? i
  ... | no  _ = []
  ... | yes w<i with xs .uncons (<⇒≺ _ _ w<i)
  ... | y , ◃ ys = y ∷ take′ _ ys

  take : 𝑆 → Stream A → List A
  take x xs = take′ x xs
