\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Algebra

module Control.Monad.Weighted.Eliminators {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels
open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Functor rng
open import Control.Monad.Weighted.Functor.TypeDef
open import Data.Sigma

private
  variable
    p q : Level
    P : Weighted A → Type p
    Q : Weighted A → Type q

module _ {A : Type a} {P : Weighted A → Type p} where
\end{code}
%<*coherent>
\begin{code}
  record Coherent (ψ : Alg A P) : Type (p ℓ⊔ a ℓ⊔ ℓ) where
    field  c-set : ∀ xs → isSet (P xs)
           c-dup : ∀ p q x xs ψ⟨xs⟩ →    ψ (p  ◃ x ∷ (q ◃ x ∷ xs) ⟨ ψ (q ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)
                                           ≡[ i ≔ P (dup p q x xs i)   ]≡
                                             ψ ((p + q) ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩)
           c-com : ∀ p x q y xs ψ⟨xs⟩ →  ψ (p  ◃ x ∷ (q ◃ y ∷ xs) ⟨ ψ (q ◃ y ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)
                                           ≡[ i ≔ P (com p x q y xs i) ]≡
                                             ψ (q ◃ y ∷ (p ◃ x ∷ xs) ⟨ ψ (p ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)
           c-del : ∀ x xs ψ⟨xs⟩ →        ψ (0# ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ≡[ i ≔ P (del x xs i) ]≡ ψ⟨xs⟩
\end{code}
%</coherent>
\begin{code}
open Coherent public
\end{code}
%<*elim-decl>
\begin{code}
Ψ :  (A : Type a) (P : Weighted A → Type p) →
     Type _
Ψ A P = Σ (Alg A P) Coherent
\end{code}
%</elim-decl>
\begin{code}
infixr 1 Ψ
syntax Ψ A (λ v → e) = Ψ[ v ⦂ A ] e

\end{code}
%<*recursor-decl>
\begin{code}
Φ : Type a → Type b → Type (a ℓ⊔ b ℓ⊔ ℓ)
Φ A B = Ψ A (λ _ → B)
\end{code}
%</recursor-decl>
%<*runner-ty>
\begin{code}
⟦_⟧ : Ψ A P → (xs : Weighted A) → P xs
\end{code}
%</runner-ty>
\begin{code}
⟦ alg ⟧ []                    = alg .fst []
⟦ alg ⟧ (p ◃ x ∷ xs)          = alg .fst (p ◃ x ∷ xs ⟨ ⟦ alg ⟧ xs ⟩)
⟦ alg ⟧ (dup p q x xs i)      = alg .snd .c-dup p q x xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (com p x q y xs i)    = alg .snd .c-com p x q y xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (del x xs i)          = alg .snd .c-del x xs (⟦ alg ⟧ xs) i
⟦ alg ⟧ (trunc xs ys p q i j) =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-set)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc xs ys p q)
    i j

prop-coh : {A : Type a} {P : Weighted A → Type p} {alg : Alg A P} → (∀ xs → isProp (P xs)) → Coherent alg
prop-coh P-isProp .c-set xs = isProp→isSet (P-isProp xs)
prop-coh {P = P} {alg = alg} P-isProp .c-dup p q x xs ψ⟨xs⟩ =
 toPathP (P-isProp (p + q ◃ x ∷ xs) (transp (λ i → P (dup p q x xs i)) i0 (alg (p ◃ x ∷ (q ◃ x ∷ xs) ⟨ alg (q ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg ((p + q) ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩)))
prop-coh {P = P} {alg = alg} P-isProp .c-com p x q y xs ψ⟨xs⟩ =
  toPathP (P-isProp (q ◃ y ∷ p ◃ x ∷ xs) (transp (λ i → P (com p x q y xs i)) i0 (alg (p ◃ x ∷ (q ◃ y ∷ xs) ⟨ alg (q ◃ y ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩))) (alg (q ◃ y ∷ (p ◃ x ∷ xs) ⟨ alg (p ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩) ⟩)))
prop-coh {P = P} {alg = alg} P-isProp .c-del x xs ψ⟨xs⟩ =
  toPathP (P-isProp xs (transp (λ i → P (del x xs i)) i0 (alg (0# ◃ x ∷ xs ⟨ ψ⟨xs⟩ ⟩))) ψ⟨xs⟩)

infix 4 _⊜_
record AnEquality (A : Type a) : Type (a ℓ⊔ ℓ) where
  constructor _⊜_
  field lhs rhs : Weighted A
open AnEquality public

EqualityProof-Alg : {B : Type b} (A : Type a) (P : Weighted A → AnEquality B) → Type (a ℓ⊔ b ℓ⊔ ℓ)
EqualityProof-Alg A P = Alg A (λ xs → let Pxs = P xs in lhs Pxs ≡ rhs Pxs)

eq-coh : {A : Type a} {B : Type b} {P : Weighted A → AnEquality B} {alg : EqualityProof-Alg A P} → Coherent alg
eq-coh {P = P} = prop-coh λ xs → let Pxs = P xs in trunc (lhs Pxs) (rhs Pxs)
\end{code}
