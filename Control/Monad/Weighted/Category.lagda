\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import HLevels
open import Level

module Control.Monad.Weighted.Category {ℓ} {𝑅 : Type ℓ} (rng : Semiring 𝑅) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import Data.Sigma
open import Function hiding (_∘_; id)
open import Prelude hiding (_∘_; id)

open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Functor rng
open import Control.Monad.Weighted.Functor.TypeDef

module _ {v} {V : Type v} {𝒸 : Level} where

  W-Alg : Type _
\end{code}
%<*w-alg>
\begin{code}
  W-Alg = Σ[ A ⦂ (Weighted V → Type 𝒸) ] × Ψ V A
\end{code}
%</w-alg>
\begin{code}
  _⟶_ : W-Alg → W-Alg → Type _
\end{code}
%<*w-alg-hom>
\begin{code}
  (A , a) ⟶ (B , b) = Σ[ h ⦂ (A ⇒ B) ] × ∀ xs → h (a .fst xs) ≡[ i ≔ B (map-id h xs i) ]≡ b .fst (map h xs)
\end{code}
%</w-alg-hom>
\begin{code}

  private variable X Y Z : W-Alg

\end{code}
%<*id>
\begin{code}
  id : X ⟶ X
  id .fst x = x
  id .snd []                 = refl
  id .snd (_ ◃ _ ∷ _ ⟨ _ ⟩)  = refl
\end{code}
%</id>
\begin{code}
  module _ {X Y Z : W-Alg} where
\end{code}
%<*comp>
\begin{code}
    _∘_ : (Y ⟶ Z) → (X ⟶ Y) → (X ⟶ Z)
    (f ∘ g) .fst x = f .fst (g .fst x)
    (f ∘ g) .snd [] =
      f .fst (g .fst (X .snd .fst []))  ≡⟨ cong (f .fst) (g .snd []) ⟩
      f .fst (Y .snd .fst [])           ≡⟨ f .snd [] ⟩
      Z .snd .fst [] ∎
    (f ∘ g) .snd (p ◃ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
      f .fst (g .fst (X .snd .fst (p ◃ x ∷ xs ⟨ P⟨xs⟩ ⟩)))  ≡⟨ cong (f .fst) (g .snd (p ◃ x ∷ xs ⟨ P⟨xs⟩ ⟩)) ⟩
      f .fst (Y .snd .fst (p ◃ x ∷ xs ⟨ g .fst P⟨xs⟩ ⟩))    ≡⟨ f .snd (p ◃ x ∷ xs ⟨ g .fst P⟨xs⟩ ⟩) ⟩
      Z .snd .fst (p ◃ x ∷ xs ⟨ f .fst (g .fst P⟨xs⟩) ⟩) ∎
\end{code}
%</comp>
