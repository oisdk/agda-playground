\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Level

module Control.Monad.Weighted.Cond {ℓ} {𝑅 : Type ℓ} (rng : Semiring 𝑅) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Data.Sigma

open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Union rng

open import Control.Monad.Weighted.Functor rng
open import Control.Monad.Weighted.Functor.TypeDef
\end{code}
%<*cond-alg>
\begin{code}
⋊-alg : 𝑅 → Φ A (Weighted A)
⋊-alg w .fst (p ◃ x ∷ xs ⟨ w⋊xs ⟩)  = (w * p) ◃ x ∷ w⋊xs
⋊-alg w .fst []                     = []
\end{code}
%</cond-alg>
%<*cond-coh>
\begin{code}
⋊-alg w .snd .c-com p x q  y xs w⋊xs = com (w * p) x (w * q) y w⋊xs

⋊-alg w .snd .c-dup p q x xs w⋊xs =
                             w * p ◃ x ∷ w * q ◃ x ∷ w⋊xs  ≡⟨ dup (w * p) (w * q) x w⋊xs ⟩
                             w * p + w * q ◃ x ∷ w⋊xs      ≡˘⟨ cong (_◃ x ∷ w⋊xs) (*⟨+⟩ w p q) ⟩
                             w * (p + q) ◃ x ∷ w⋊xs ∎

⋊-alg w .snd .c-del x xs w⋊xs =
                             w * 0# ◃ x ∷ w⋊xs  ≡⟨ cong (_◃ x ∷ w⋊xs) (*0 w) ⟩
                             0# ◃ x ∷ w⋊xs      ≡⟨ del x w⋊xs ⟩
                             w⋊xs ∎
\end{code}
%</cond-coh>
\begin{code}
⋊-alg c .snd .c-set _ = trunc

infixr 5.5 _⋊_
\end{code}
%<*cond-impl>
\begin{code}
_⋊_ : 𝑅 → Weighted A → Weighted A
x ⋊ xs = ⟦ ⋊-alg x ⟧ xs
\end{code}
%</cond-impl>
\begin{code}

_ : ∀ {w w₁ w₂ w₃} → {x y z : A} →
\end{code}
%<*cond-example>
\begin{code}
  w ⋊ (w₁ ◃ x ∷ w₂ ◃ y ∷ w₃ ◃ z ∷ []) ≡ (w * w₁) ◃ x ∷ (w * w₂) ◃ y ∷ (w * w₃) ◃ z ∷ []
\end{code}
%</cond-example>
\begin{code}
_ = refl

⋊-distribʳ : ∀ p q → (xs : Weighted A) → (p ⋊ xs) ∪ (q ⋊ xs) ≡ p + q ⋊ xs
⋊-distribʳ p q = ⟦ ⋊-distribʳ′ p q ⟧
  where
  ⋊-distribʳ′ : ∀ p q → Ψ[ xs ⦂ A ] (p ⋊ xs) ∪ (q ⋊ xs) ≡ (p + q) ⋊ xs
  ⋊-distribʳ′ p q .fst [] = refl
  ⋊-distribʳ′ p q .fst (r ◃ x ∷ xs ⟨ P ⟩) =
    (p ⋊ (r ◃ x ∷ xs)) ∪ (q ⋊ (r ◃ x ∷ xs))  ≡˘⟨ ∪-cons (q * r) x (p ⋊ (r ◃ x ∷ xs)) (q ⋊ xs)  ⟩
    q * r ◃ x ∷ (p ⋊ (r ◃ x ∷ xs)) ∪ q ⋊ xs  ≡⟨ cong (_∪ q ⋊ xs) (dup (q * r) (p * r) x (p ⋊ xs)) ⟩
    q * r + p * r ◃ x ∷ (p ⋊ xs) ∪ q ⋊ xs    ≡˘⟨ cong (_◃ x ∷ ((p ⋊ xs) ∪ (q ⋊ xs))) (⟨+⟩* q p r) ⟩
    (q + p) * r ◃ x ∷ (p ⋊ xs) ∪ (q ⋊ xs)    ≡⟨ cong ((q + p) * r ◃ x ∷_) P ⟩
    (q + p) * r ◃ x ∷ (p + q) ⋊ xs           ≡⟨ cong (λ pq → pq * r ◃ x ∷ (p + q) ⋊ xs) (+-comm q p) ⟩
    (p + q) * r ◃ x ∷ (p + q) ⋊ xs           ≡⟨⟩
    (p + q) ⋊ (r ◃ x ∷ xs) ∎
  ⋊-distribʳ′ p q .snd = eq-coh

⋊-distribˡ : ∀ p → (xs ys : Weighted A) → (p ⋊ xs) ∪ (p ⋊ ys) ≡ p ⋊ (xs ∪ ys)
⋊-distribˡ = λ p xs ys → ⟦ ⋊-distribˡ′ p ys ⟧ xs
  module JDistribL where
  ⋊-distribˡ′ : ∀ p ys → Ψ[ xs ⦂ A ] (p ⋊ xs) ∪ (p ⋊ ys) ≡ p ⋊ (xs ∪ ys)
  ⋊-distribˡ′ p ys .fst [] = refl
  ⋊-distribˡ′ p ys .fst (q ◃ x ∷ xs ⟨ P ⟩) = cong (p * q ◃ x ∷_) P
  ⋊-distribˡ′ p ys .snd = eq-coh

0⋊ : (xs : Weighted A) → 0# ⋊ xs ≡ []
0⋊ = ⟦ 0⋊′ ⟧
  where
  0⋊′ : Ψ[ xs ⦂ A ] 0# ⋊ xs ≡ []
  0⋊′ .fst [] = refl
  0⋊′ .fst (p ◃ x ∷ xs ⟨ P ⟩) =
    0# ⋊ (p ◃ x ∷ xs)     ≡⟨⟩
    0# * p ◃ x ∷ 0# ⋊ xs  ≡⟨ cong (_◃ x ∷ 0# ⋊ xs) (0* p) ⟩
    0# ◃ x ∷ 0# ⋊ xs      ≡⟨ del x (0# ⋊ xs) ⟩
    0# ⋊ xs               ≡⟨ P ⟩
    [] ∎
  0⋊′ .snd = eq-coh

1⋊ : (xs : Weighted A) → 1# ⋊ xs ≡ xs
1⋊ = ⟦ 1⋊′ ⟧
  where
  1⋊′ : Ψ[ xs ⦂ A ] 1# ⋊ xs ≡ xs
  1⋊′ .fst [] = refl
  1⋊′ .fst (p ◃ x ∷ xs ⟨ P ⟩) =
    1# ⋊ (p ◃ x ∷ xs) ≡⟨⟩
    1# * p ◃ x ∷ 1# ⋊ xs ≡⟨ cong (_◃ x ∷ 1# ⋊ xs) (1* p) ⟩
    p ◃ x ∷ 1# ⋊ xs ≡⟨ cong (p ◃ x ∷_) P ⟩
    p ◃ x ∷ xs ∎
  1⋊′ .snd = eq-coh

*-assoc-⋊ : ∀ p q (xs : Weighted A) → (p * q) ⋊ xs ≡ p ⋊ (q ⋊ xs)
*-assoc-⋊ p q = ⟦ *-assoc-⋊′ p q ⟧
  where
  *-assoc-⋊′ : ∀ p q → Ψ[ xs ⦂ A ] (p * q) ⋊ xs ≡ p ⋊ (q ⋊ xs)
  *-assoc-⋊′ p q .fst [] = refl
  *-assoc-⋊′ p q .fst (r ◃ x ∷ xs ⟨ P ⟩) =
    p * q ⋊ (r ◃ x ∷ xs) ≡⟨⟩
    p * q * r ◃ x ∷ (p * q ⋊ xs) ≡⟨ cong (_◃ x ∷ (p * q ⋊ xs)) (*-assoc p q r) ⟩
    p * (q * r) ◃ x ∷ (p * q ⋊ xs) ≡⟨ cong (p * (q * r) ◃ x ∷_) P ⟩
    p * (q * r) ◃ x ∷ (p ⋊ (q ⋊ xs)) ≡⟨⟩
    p ⋊ (q ⋊ (r ◃ x ∷ xs)) ∎
  *-assoc-⋊′ p q .snd = eq-coh

⋊∅ : (x : 𝑅) → x ⋊ ([] {A = A}) ≡ []
⋊∅ x = refl
\end{code}
