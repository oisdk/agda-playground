{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra
open import Algebra.Monus

module Control.Monad.Weighted.Depth {ℓ} (mon : TMAPOM ℓ) where

open TMAPOM mon

Rng : Semiring _
Rng = viterbi tapom


open import Level
open import Path
open import HLevels
open import Prelude

open import Control.Monad.Weighted Rng
open import Control.Monad.Weighted.Eliminators Rng
open import Control.Monad.Weighted.Functor Rng hiding (⟪_⟫)
open import Control.Monad.Weighted.Functor.TypeDef

record Tree (A : Type a) : Type (a ℓ⊔ ℓ) where
  coinductive; no-eta-equality
  constructor _◀_
  field
    root : A
    rest : Weighted (Tree A)
open Tree public
            
-- need to add an Acc here
module _ (wf : WellFounded _≺_) where
  restrictₛ : 𝑆 → Weighted (Tree A) → Weighted A
  restrictₛ w = ⟦ restrict-alg w (wf w) ⟧
    where
    restrict-alg : ∀ w → Acc _≺_ w → Φ (Tree A) (Weighted A)
    restrict-alg w _ .fst [] = []
    restrict-alg w _ .fst (nothing ◃ x ∷ _ ⟨ P⟨xs⟩ ⟩) = P⟨xs⟩
    restrict-alg w (acc wf) .fst (just w′ ◃ x ∷ _ ⟨ P⟨xs⟩ ⟩) with w′ ≤? w
    ... | no  w′>w = P⟨xs⟩
    ... | yes (k , w′≤w) = (just ε ◃ root x ∷ just w′ ⋊ ⟦ restrict-alg k (wf _ {!!}) ⟧ (rest x)) ∪ P⟨xs⟩
    restrict-alg w _ .snd .c-set _ = trunc
    restrict-alg w (acc wf) .snd .c-dup nothing  nothing  x xs ψ⟨xs⟩ = refl
    restrict-alg w (acc wf) .snd .c-dup nothing  (just q) x xs ψ⟨xs⟩ = refl
    restrict-alg w (acc wf) .snd .c-dup (just p) nothing  x xs ψ⟨xs⟩ with p ≤? w
    ... | yes (k , p≤w) = refl
    ... | no p>w = refl
    restrict-alg w (acc wf) .snd .c-dup (just p) (just q) x xs ψ⟨xs⟩ with p ≤? w | q ≤? w
    ... | no  p>w        | no  q>w        = {!!}
    ... | yes (k₁ , p≤w) | no  q>w        = {!!}
    ... | no  p>w        | yes (k₂ , q≤w) = {!!}
    ... | yes (k₁ , p≤w) | yes (k₂ , q≤w) = {!!}
    restrict-alg w (acc wf) .snd .c-com nothing  x nothing  y xs ψ⟨xs⟩ = refl
    restrict-alg w (acc wf) .snd .c-com nothing  x (just q) y xs ψ⟨xs⟩ = {!!}
    restrict-alg w (acc wf) .snd .c-com (just p) x nothing  y xs ψ⟨xs⟩ = {!!}
    restrict-alg w (acc wf) .snd .c-com (just p) x (just q) y xs ψ⟨xs⟩ with p ≤? w
    ... | yes (k , p≤w) = {!!}
    ... | no  p>w       = {!!}
    restrict-alg w (acc _) .snd .c-del x xs ψ⟨xs⟩ = refl

