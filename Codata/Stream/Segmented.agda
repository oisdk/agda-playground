{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Stream.Segmented
  {ℓ}
  (mon : TMAPOM ℓ)
  (𝓌𝒻 : WellFounded (TMAPOM._<_ mon))
  (cancelˡ : Cancellativeˡ (TMAPOM._∙_ mon))
  where

open TMAPOM mon

module Approach1 where
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

  ≤-pos-< : ∀ x y → (x≤y : x ≤ y) → fst x≤y ≢ ε → x < y
  ≤-pos-< x y (k₁ , y≡x∙k₁) k₁≢ε (k₂ , x≡y∙k₂) =
    k₁≢ε (zeroSumFree k₁ k₂ (sym (cancelˡ x ε (k₁ ∙ k₂) (∙ε x ; x≡y∙k₂ ; cong (_∙ k₂) y≡x∙k₁ ; assoc x k₁ k₂))))

  module _ (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
    repeat′ : Acc _<_ i → Stream′ A i
    repeat′ a .head = x
    repeat′ a .size = s
    repeat′ (acc wf) .tail (k , p) = just (repeat′ (wf _ (≤-pos-< k _ (s , p ; comm s k) s≢ε)))

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

module Approach2 where
  _∸_ : 𝑆 → 𝑆 → 𝑆
  x ∸ y = (fst ▿ fst) (x ≤|≥ y)

  record Stream′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
    inductive
    field
      weight : 𝑆
      uncons : (w<i : weight < i) → A × Stream′ A (i ∸ weight)
  open Stream′ public

  private
    variable
      i j : 𝑆

  Stream : Type a → Type (a ℓ⊔ ℓ)
  Stream A = ∀ {i} → Stream′ A i

  lemma₁ : ∀ x y → x < y → x ≢ ε → y ∸ x < y
  lemma₁ = {!!}

  lemma₂ : ∀ x → ¬ (x < x ∸ ε)
  lemma₂ = {!!}

  pure : A → Stream A
  pure x .weight = ε
  pure x .uncons ε<i .fst = x
  pure x {i} .uncons ε<i .snd .weight = i
  pure x .uncons ε<i .snd .uncons i<i∸ε = ⊥-elim (lemma₂ _ i<i∸ε)

  module _ (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
    repeat′ : Acc _<_ i → Stream′ A i
    repeat′ a .weight = s
    repeat′ a .uncons s<i .fst = x
    repeat′ {i} (acc wf) .uncons s<i .snd = repeat′ (wf _ (lemma₁ s i s<i s≢ε))

    repeat : Stream A
    repeat = repeat′ (𝓌𝒻 _)

  -- map : (A → B) → Stream′ A i → Stream′ B i
  -- map f xs .weight = xs .weight
  -- map f xs .uncons w<i = case xs .uncons w<i of λ { (y , ys) → f y , map f ys }
