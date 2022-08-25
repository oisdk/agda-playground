{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra
open import Algebra.Monus
open import Level

module Control.Monad.Weighted.Depth {ℓ} {𝑆 : Type ℓ} (mon : TMAPOM 𝑆) where

open TMAPOM mon

Rng : Semiring _
Rng = viterbi _ tapom


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
            
module _ (wf : WellFounded _≺_) where
  restrictₛ : 𝑆 → Weighted (Tree A) → Weighted A
  restrictₛ w = ⟦ restrict-alg w (wf w) ⟧
    where
    restrict-alg : ∀ w → Acc _≺_ w → Φ (Tree A) (Weighted A)
    restrict-alg w _ .fst [] = []
    restrict-alg w _ .fst (nothing ◃ x ∷ _ ⟨ P⟨xs⟩ ⟩) = P⟨xs⟩
    restrict-alg w (acc wf) .fst (just w′ ◃ x ∷ _ ⟨ P⟨xs⟩ ⟩) with w′ ≤? w
    ... | no  w′>w = P⟨xs⟩
    ... | yes (k , w′≤w) = (just ε ◃ root x ∷ just w′ ⋊ ⟦ restrict-alg k (wf _ (w′ , w′≤w ; comm _ _ , {!!})) ⟧ (rest x)) ∪ P⟨xs⟩
    restrict-alg w _ .snd .c-set _ = trunc
    restrict-alg w (acc wf) .snd .c-dup nothing  nothing  x xs ψ⟨xs⟩ = refl
    restrict-alg w (acc wf) .snd .c-dup nothing  (just q) x xs ψ⟨xs⟩ = refl
    restrict-alg w (acc wf) .snd .c-dup (just p) nothing  x xs ψ⟨xs⟩ = {!!}
    restrict-alg w (acc wf) .snd .c-dup (just p) (just q) x xs ψ⟨xs⟩ = {!!}
    restrict-alg w (acc wf) .snd .c-com nothing  x nothing  y xs ψ⟨xs⟩ = refl
    restrict-alg w (acc wf) .snd .c-com nothing  x (just q) y xs ψ⟨xs⟩ = {!!}
    restrict-alg w (acc wf) .snd .c-com (just p) x nothing  y xs ψ⟨xs⟩ = {!!}
    restrict-alg w (acc wf) .snd .c-com (just p) x (just q) y xs ψ⟨xs⟩ = {!!}
    restrict-alg w (acc _) .snd .c-del x xs ψ⟨xs⟩ = refl

