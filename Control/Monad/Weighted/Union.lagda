\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Algebra
open import Level

module Control.Monad.Weighted.Union {ℓ} {𝑅 : Type ℓ} (rng : Semiring 𝑅) where

open Semiring rng

open import Level
open import Path
open import HLevels
open import Data.Sigma
open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Functor rng
open import Control.Monad.Weighted.Functor.TypeDef

\end{code}
%<*union-alg>
\begin{code}
∪-alg : Weighted A → Φ A (Weighted A)
∪-alg ys .fst []                  = ys
∪-alg ys .fst (w ◃ x ∷ _ ⟨ xs ⟩)  = w ◃ x ∷ xs
\end{code}
%</union-alg>
%<*union-coh>
\begin{code}
∪-alg ys .snd .c-dup p q x _ r = dup p q x r
∪-alg ys .snd .c-com p x q y _ r = com p x q y r
∪-alg ys .snd .c-del x _ r = del x r
\end{code}
%</union-coh>
\begin{code}
∪-alg ys .snd .c-set _ = trunc

infixr 5 _∪_
\end{code}
%<*union-impl>
\begin{code}
_∪_ : Weighted A → Weighted A → Weighted A
xs ∪ ys = ⟦ ∪-alg ys ⟧ xs
\end{code}
%</union-impl>
\begin{code}
∪-assoc : (xs ys zs : Weighted A) → xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs
∪-assoc xs ys zs = ⟦ ∪-assoc′ ys zs ⟧ xs
  where
  ∪-assoc′ : ∀ ys zs → Ψ[ xs ⦂ A ] xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs
  ∪-assoc′ ys zs .fst [] = refl
  ∪-assoc′ ys zs .fst (p ◃ x ∷ xs ⟨ P ⟩) = cong (p ◃ x ∷_) P
  ∪-assoc′ ys zs .snd = eq-coh

∪-idr : (xs : Weighted A) → xs ∪ [] ≡ xs
∪-idr = ⟦ ∪-idr′ ⟧
  where
  ∪-idr′ : Ψ[ xs ⦂ A ] xs ∪ [] ≡ xs
  ∪-idr′ .fst [] = refl
  ∪-idr′ .fst (p ◃ x ∷ xs ⟨ Pxs ⟩) = cong (p ◃ x ∷_) Pxs
  ∪-idr′ .snd = eq-coh

∪-cons : ∀ p x (xs ys : Weighted A) → p ◃ x ∷ xs ∪ ys ≡ xs ∪ p ◃ x ∷ ys
∪-cons p x xs ys = ⟦ ∪-cons′ p x ys ⟧ xs
  where
  ∪-cons′ : ∀ p x ys → Ψ[ xs ⦂ A ] p ◃ x ∷ xs ∪ ys ≡ xs ∪ p ◃ x ∷ ys
  ∪-cons′ p x ys .fst (q ◃ y ∷ xs ⟨ Pxs ⟩) = com p x q y (xs ∪ ys) ; cong (q ◃ y ∷_) Pxs
  ∪-cons′ p x ys .fst [] = refl
  ∪-cons′ p x ys .snd = eq-coh

∪-com : (xs ys : Weighted A) → xs ∪ ys ≡ ys ∪ xs
∪-com xs ys = ⟦ ∪-com′ ys ⟧ xs
  where
  ∪-com′ : ∀ ys → Ψ[ xs ⦂ A ] xs ∪ ys ≡ ys ∪ xs
  ∪-com′ ys .fst (p ◃ x ∷ xs ⟨ Pxs ⟩) = cong (p ◃ x ∷_) Pxs ; ∪-cons p x ys xs
  ∪-com′ ys .fst [] = sym (∪-idr ys)
  ∪-com′ ys .snd = eq-coh
\end{code}
