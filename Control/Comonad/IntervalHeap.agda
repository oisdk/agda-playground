{-# OPTIONS --cubical --safe --postfix-projections --guardedness #-}

open import Algebra
open import Prelude
open import Relation.Binary
open import WellFounded
open import Algebra.Monus
open import Data.Maybe

module Control.Comonad.IntervalHeap {s}
  (mon : Monus s)
  (wf : WellFounded (Monus._<_ mon))
  (cancel : Cancellativeˡ (Monus._∙_ mon))
  where

open Monus mon

mutual
  record Heap (A : Type a) : Type (s ℓ⊔ a) where
    inductive; constructor _≺_
    field
      hd : A
      tl : Next A

  record Next {a} (A : Type a) : Type (s ℓ⊔ a) where
    coinductive; constructor ⟪_⟫
    field next : Span A

  data Span {a} (A : Type a) : Type (s ℓ⊔ a) where
    [] : Span A
    until : (s : 𝑆) → (s≢ε : s ≢ ε) → (xs : Heap A) → Span A
open Heap public
open Next public

State : Type a → Type _
State A = 𝑆 → A × 𝑆

pop′ : (s : 𝑆) → Acc _<_ s → Heap A → A × 𝑆
pop′ s₂ a xs with xs .tl .next
pop′ s₂ a xs | [] = xs .hd , ε
pop′ s₂ a xs | until s₁ s₁≢ε ys with s₁ ≤? s₂
pop′ s₂ a xs | until s₁ s₁≢ε ys | no s₁≰s₂ = xs .hd , fst (<⇒≤ s₁≰s₂)
pop′ s₂ (acc wf) xs | until s₁ s₁≢ε ys | yes (k₁ , s₂≡s₁∙k₁) = pop′ k₁ (wf k₁ lemma) ys
  where
  lemma : k₁ < s₂
  lemma (k₂ , k₁≡s₂∙k₂) = s₁≢ε (zeroSumFree s₁ k₂ (sym (cancel k₁ _ _ p)))
    where
    p : k₁ ∙ ε ≡ k₁ ∙ (s₁ ∙ k₂)
    p = ∙ε k₁ ; k₁≡s₂∙k₂ ; cong (_∙ k₂) s₂≡s₁∙k₁ ; cong (_∙ k₂) (comm s₁ k₁) ; assoc k₁ s₁ k₂

pop : Heap A → State A
pop xs s = pop′ s (wf s) xs

mutual
  stepFrom : State A → (s : 𝑆) → Dec (s ≡ ε) → Span A
  stepFrom f s (yes p) = []
  stepFrom f s (no ¬p) = until s ¬p (tabulate (f ∘ (s ∙_)))

  tabulate : State A → Heap A
  tabulate f =
    let x , s = f ε
    in x ≺ λ where .next → stepFrom f s (s ≟ ε)

pop-ε : (xs : Heap A) (a : Acc _<_ ε) → pop′ ε a xs .fst ≡ xs .hd
pop-ε xs _ with xs .tl .next
pop-ε xs _ | [] = refl
pop-ε xs _ | until s s≢ε ys with s ≤? ε
pop-ε xs _ | until s s≢ε ys | no  s≰ε = refl
pop-ε xs _ | until s s≢ε ys | yes s≤ε = ⊥-elim (s≢ε (antisym s≤ε (positive {s})))

-- slide : Heap A → Heap A
-- slide xs with xs .tl .next
-- slide xs | [] = xs
-- slide xs | [] = []

-- pop-tl : ∀ (x : A) s₁ (s₁≢ε : s₁ ≢ ε) xs s₂ → pop (x ≺ ⟪ until s₁ s₁≢ε xs ⟫) (s₁ ∙ s₂) ≡ pop xs s₂
-- pop-tl x s₁ s₁≢ε xs s₂ with s₁ ≤? (s₁ ∙ s₂)
-- pop-tl x s₁ s₁≢ε xs s₂ | no  s₁≰s₁∙s₂ = ⊥-elim (s₁≰s₁∙s₂ (s₂ , refl))
-- pop-tl x s₁ s₁≢ε xs s₂ | yes (k , s₁≤s₁∙s₂) =
--   let p = cancel s₁ s₂ k s₁≤s₁∙s₂
--   in {!!} ; cong (λ w → pop′ s₂ w xs) (isPropAcc {!!} (wf s₂))

-- seg-leftInv′ : (x : Heap A) → tabulate (pop x) ≡ x
-- seg-leftInv′ x = {!!}

-- mutual
--   seg-leftInv′ : (xs : Heap A) → stepFrom (pop xs) (pop xs ε .snd) (pop xs ε .snd ≟ ε) ≡ xs .tl .next
--   seg-leftInv′ (x ≺ xs) with pop (x ≺ xs) ε .snd ≟ ε
--   seg-leftInv′ (x ≺ xs) | yes s≡ε = {!!}
--   seg-leftInv′ (x ≺ xs) | no  s≢ε = {!!}

--   seg-leftInv : (x : Heap A) → tabulate (pop x) ≡ x
--   seg-leftInv (x ≺ xs) i .hd = pop-ε (x ≺ xs) (wf ε) i
--   seg-leftInv (x ≺ xs) i .tl .next = seg-leftInv′ (x ≺ xs) i

-- state-iso : Heap A ⇔ State A
-- state-iso .fun = pop
-- state-iso .inv = tabulate
-- state-iso .rightInv = {!!}
-- state-iso .leftInv  = {!!}
