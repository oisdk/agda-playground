{-# OPTIONS --cubical --safe --postfix-projections --guardedness #-}

open import Algebra
open import Prelude
open import Relation.Binary
open import WellFounded
open import Algebra.Monus
open import Data.Maybe

module Control.Comonad.IntervalHeap {s}
  (mon : Monus s)
  (absorbative : Monus.Absorbative mon)
  (wf : WellFounded (Monus._<_ mon)) where

open Monus mon public renaming (total⇒discrete to _≟_)

record Heap {a} (A : Type a) : Type (s ℓ⊔ a) where
  coinductive; constructor _≺_
  field
    v : A
    next : Maybe (∃[ s ] ((s ≢ ε) × Heap A))
open Heap public

State : Type a → Type _
State A = 𝑆 → A × 𝑆

pop′ : (s : 𝑆) → Acc _<_ s → Heap A → A × 𝑆
pop′ s₂ a xs with xs .next
pop′ s₂ a xs | nothing = xs .v , ε
pop′ s₂ a xs | just (s₁ , s₁≢ε , ys) with s₁ ≤? s₂
pop′ s₂ a xs | just (s₁ , s₁≢ε , ys) | no s₁≰s₂ = xs .v , fst (<⇒≤ s₁≰s₂)
pop′ s₂ (acc wf) xs | just (s₁ , s₁≢ε , ys) | yes (k₁ , s₂≡s₁∙k₁) = pop′ k₁ (wf k₁ lemma) ys
  where
  lemma : k₁ < s₂
  lemma (k₂ , k₁≡s₂∙k₂) = s₁≢ε (zeroSumFree s₁ k₂ (absorbative _ _ p))
    where
    p : k₁ ≡ k₁ ∙ (s₁ ∙ k₂)
    p = k₁≡s₂∙k₂ ; cong (_∙ k₂) s₂≡s₁∙k₁ ; cong (_∙ k₂) (comm s₁ k₁) ; assoc k₁ s₁ k₂

pop : Heap A → State A
pop xs s = pop′ s (wf s) xs

mutual
  stepFrom : State A → (s : 𝑆) → Dec (s ≡ ε) → Maybe (∃[ s ] ((s ≢ ε) × Heap A))
  stepFrom f s (yes p) = nothing
  stepFrom f s (no ¬p) = just (s , ¬p , tabulate (f ∘′ _∙_ s))

  tabulate : State A → Heap A
  tabulate f = let x , s = f ε in λ where
    .v → x
    .next → stepFrom f s (s ≟ ε)

-- mutual
--   seg-rightInv″ : (f : State A) (s₁ : 𝑆) (a : Acc _<_ s₁) (x : A) (s₂ : 𝑆) (p : Dec (s₂ ≡ ε)) → pop′ s₁ a (x ≺ stepFrom f s₂ p) ≡ f s₁
--   seg-rightInv″ f s₁ a x s₂ p = {!!}

--   seg-rightInv′ : (f : State A) (s : 𝑆) (a : Acc _<_ s) → pop′ s a (tabulate f) ≡ f s
--   seg-rightInv′ f s a = let x , s₂ = f ε in seg-rightInv″ f s a x s₂ (s₂ ≟ ε)

-- seg-rightInv : (x : State A) → pop (tabulate x) ≡ x
-- seg-rightInv x = funExt (λ s → seg-rightInv′ x s (wf s))

-- seg-leftInv : (x : Heap A) → tabulate (pop x) ≡ x
-- seg-leftInv = {!!}

-- state-iso : Heap A ⇔ State A
-- state-iso .fun = pop
-- state-iso .inv = tabulate
-- state-iso .rightInv = seg-rightInv
-- state-iso .leftInv  = seg-leftInv
