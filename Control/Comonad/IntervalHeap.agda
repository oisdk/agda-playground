{-# OPTIONS --cubical --safe --postfix-projections --guardedness #-}

open import Algebra
open import Prelude
open import Relation.Binary
open import WellFounded
open import Algebra.Monus

module Control.Comonad.IntervalHeap {s}
  (mon : Monus s)
  (absorbative : Monus.Absorbative mon)
  (wf : WellFounded (Monus._<_ mon)) where

open Monus mon public

record Heap {a} (A : Type a) : Type (s ℓ⊔ a) where
  coinductive
  constructor _:[⋯_⟨_⟩],_
  field
    v : A
    w : 𝑆
    w≢ε : w ≢ ε
    rs : Heap A
open Heap public

State : Type a → Type _
State A = 𝑆 → ∃[ w ] (w ≢ ε) × A

pop′ : Heap A → (w : 𝑆) → Acc _<_ w → ∃[ w ] (w ≢ ε) × A
pop′ xs s₂ r with w xs ≤? s₂
pop′ xs s₂ r | no s₁≰s₂ = let k , p = <⇒≤ s₁≰s₂ in k , diff≢ε s₁≰s₂ , v xs
pop′ xs s₂ (acc wf) | yes (k₁ , s₂≡s₁∙k₁) = pop′ (rs xs) k₁ (wf k₁ lemma)
  where
  s₁ = w xs

  lemma : k₁ < s₂
  lemma (k₂ , k₁≡s₂∙k₂) = w≢ε xs (zeroSumFree s₁ k₂ (absorbative _ _ p))
    where
    p : k₁ ≡ k₁ ∙ (s₁ ∙ k₂)
    p = k₁≡s₂∙k₂ ; cong (_∙ k₂) s₂≡s₁∙k₁ ; cong (_∙ k₂) (comm s₁ k₁) ; assoc k₁ s₁ k₂

pop : Heap A → State A
pop xs w = pop′ xs w (wf w)

tabulate′ : 𝑆 → State A → Heap A
tabulate′ m f = let x , y , z = f m in λ where
  .w → x
  .w≢ε → y
  .v → z
  .rs → tabulate′ (m ∙ x) f

tabulate : State A → Heap A
tabulate = tabulate′ ε

-- -- -- from∘to : ∀ (x : Heap A) → fromFunc (toFunc x) ≡ x
-- -- -- from∘to x i .weight = {!!}
-- -- -- from∘to x i .weight≢0 = {!!}
-- -- -- from∘to x i .val = {!!}
-- -- -- from∘to x i .tail = {!!}
