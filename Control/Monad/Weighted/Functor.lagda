\begin{code}
{-# OPTIONS --cubical --safe #-}
open import Algebra
open import Level

module Control.Monad.Weighted.Functor {ℓ} {𝑅 : Type ℓ} (rng : Semiring 𝑅) where

open Semiring rng

open import Level
open import Control.Monad.Weighted.Definition rng
open import Function
open import Path
open import Prelude

open import Control.Monad.Weighted.Functor.TypeDef

private
  variable
    p q : Level
    P : Weighted A → Type p
    Q : Weighted A → Type q
private
  module DisplayFunctors where
    module SimpleFunctor where
\end{code}
%<*simple-functor-def>
\begin{code}
      data 𝔚 (A : Type a) (B : Type b) :
                    Type (a ℓ⊔ b ℓ⊔ ℓ) where
        []     : 𝔚 A B
        _◃_∷_  :  𝑅 → A →
                  B → 𝔚 A B
\end{code}
%</simple-functor-def>
%<*functor-def>
\begin{code}
    data 𝔚 (A : Type a) (P : Weighted A → Type p) :
                    Type (a ℓ⊔ p ℓ⊔ ℓ) where
      []        : 𝔚 A P
      _◃_∷_⟨_⟩  :  𝑅 → A →
                  (xs : Weighted A) → P xs → 𝔚 A P
\end{code}
%</functor-def>
\begin{code}
𝔚 : (A : Type a) → (Weighted A → Type p) → Type (a ℓ⊔ p ℓ⊔ ℓ)
𝔚 A = 𝔚-F 𝑅 (Weighted A) A
\end{code}
%<*map>
\begin{code}
map : (P ⇒ Q) → 𝔚 A P → 𝔚 A Q
map f []                      = []
map f (w ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩)  =
  w ◃ x ∷ xs ⟨ f ψ⟨xs⟩ ⟩
\end{code}
%</map>
%<*wrap>
\begin{code}
⟪_⟫ : 𝔚 A P → Weighted A
⟪ [] ⟫                = []
⟪ w ◃ x ∷ xs ⟨ _ ⟩ ⟫  = w ◃ x ∷ xs
\end{code}
%</wrap>
%<*wrap-map>
\begin{code}
map-id :  (f : P ⇒ Q) (xs : 𝔚 A P) →
          ⟪ xs ⟫ ≡ ⟪ map f xs ⟫
map-id f []                 = refl
map-id f (_ ◃ _ ∷ _ ⟨ _ ⟩)  = refl
\end{code}
%</wrap-map>
%<*alg>
\begin{code}
Alg :  (A : Type a) (P : Weighted A → Type p) →
       Type _
Alg A P = (xs : 𝔚 A P) → P ⟪ xs ⟫
\end{code}
%</alg>
