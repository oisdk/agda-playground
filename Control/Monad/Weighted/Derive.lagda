\begin{code}
{-# OPTIONS --cubical --allow-unsolved-metas --postfix-projections #-}

open import Algebra
open import Algebra.Monus

module Control.Monad.Weighted.Derive {ℓ} (mon : Monus ℓ) where

open import Level
open import Path
open import HLevels
open import Data.Sigma

open Monus mon

open import Relation.Binary.Lattice totalOrder
infixr 5 _◃_∷_
\end{code}
%<*list-part>
\begin{code}
data S (A : Type a) : Type (a ℓ⊔ ℓ) where
  _◃_∷_  : 𝑀 → A → S A → S A
  []     : S A
\end{code}
%</list-part>
%<*com>
\begin{code}
  com : ∀  p x q y xs →
    p ◃ x ∷ q ◃ y ∷ xs ≡ q ◃ y ∷ p ◃ x ∷ xs
\end{code}
%</com>
%<*dup>
\begin{code}
  dup : ∀  p q x xs →
    p ◃ x ∷ q ◃ x ∷ xs ≡ p ⊓ q ◃ x ∷ xs
\end{code}
%</dup>
%<*trunc>
\begin{code}
  trunc : isSet (S A)
\end{code}
%</trunc>
\begin{code}
open import Literals.Number
open import Data.Nat.Literals
open import Data.Unit

module _ ⦃ nm : Number 𝑀 ⦄ ⦃ _ : Number.Constraint nm 2 ⦄ ⦃ _ : Number.Constraint nm 5 ⦄ where

  example : A → A → S A
  example x y =
\end{code}
%<*example-val>
\begin{code}
    2 ◃ x ∷ 5 ◃ y ∷ []
\end{code}
%</example-val>
\begin{code}
private
  variable
    p q : Level
    P : S A → Type p
    Q : S A → Type q

module SimpleFunctor where
\end{code}
%<*simple-functor-def>
\begin{code}
  data 𝔖 (A : Type a) (B : Type b) :
                Type (a ℓ⊔ b ℓ⊔ ℓ) where
    []     : 𝔖 A B
    _◃_∷_  :  𝑀 → A →
              B → 𝔖 A B
\end{code}
%</simple-functor-def>
%<*functor-def>
\begin{code}
data 𝔖 (A : Type a) (P : S A → Type p) :
                 Type (a ℓ⊔ p ℓ⊔ ℓ) where
  []        : 𝔖 A P
  _◃_∷_⟨_⟩  :  𝑀 → A →
               (xs : S A) → P xs → 𝔖 A P
\end{code}
%</functor-def>
%<*wrap>
\begin{code}
⟪_⟫ : 𝔖 A P → S A
⟪ [] ⟫                = []
⟪ w ◃ x ∷ xs ⟨ _ ⟩ ⟫  = w ◃ x ∷ xs
\end{code}
%</wrap>
%<*alg>
\begin{code}
Alg :  (A : Type a) (P : S A → Type p) →
       Type (a ℓ⊔ p ℓ⊔ ℓ)
Alg A P = (xs : 𝔖 A P) → P ⟪ xs ⟫
\end{code}
%</alg>
\begin{code}
module _ {A : Type a} {P : S A → Type p} where
\end{code}
%<*coherent>
\begin{code}
  record Coherent (ψ : Alg A P) : Type (a ℓ⊔ p ℓ⊔ ℓ) where
    field
      c-set : ∀ xs → isSet (P xs)
      c-dup : ∀ p q x xs P⟨xs⟩ →    ψ (p ◃ x ∷ (q ◃ x ∷ xs) ⟨ ψ (q ◃ x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩)
                                      ≡[ i ≔ P (dup p q x xs i) ]≡
                                        ψ ((p ⊓ q) ◃ x ∷ xs ⟨ P⟨xs⟩ ⟩)
      c-com : ∀ p x q y xs P⟨xs⟩ →  ψ (p ◃ x ∷ (q ◃ y ∷ xs) ⟨ ψ (q ◃ y ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩)
                                      ≡[ i ≔ P (com p x q y xs i) ]≡
                                        ψ (q ◃ y ∷ (p ◃ x ∷ xs) ⟨ ψ (p ◃ x ∷ xs ⟨ P⟨xs⟩ ⟩) ⟩)
\end{code}
%</coherent>
\begin{code}
open Coherent public
\end{code}
%<*elim-decl>
\begin{code}
Ψ :  (A : Type a) (P : S A → Type p) →
     Type (a ℓ⊔ p ℓ⊔ ℓ)
Ψ A P = Σ (Alg A P) Coherent
\end{code}
%</elim-decl>
\begin{code}
infixr 1 Ψ
\end{code}
%<*elim-syntax>
\begin{code}
syntax Ψ A (λ x → e) = Ψ[ x ⦂ A ] e
\end{code}
%</elim-syntax>
%<*recursor-decl>
\begin{code}
Φ : Type a → Type b → Type (a ℓ⊔ b ℓ⊔ ℓ)
Φ A B = Ψ A (λ _ → B)
\end{code}
%</recursor-decl>
%<*elim-runner>
\begin{code}
⟦_⟧ : Ψ A P → (xs : S A) → P xs
⟦ alg , coh ⟧ (w ◃ x ∷ xs)        = alg (w ◃ x ∷ xs ⟨ ⟦ alg , coh ⟧ xs ⟩)
⟦ alg , coh ⟧ []                  = alg []
⟦ alg , coh ⟧ (com p x q y xs i)  = coh .c-com p x q y xs (⟦ alg , coh ⟧ xs) i
⟦ alg , coh ⟧ (dup p q x xs i)    = coh .c-dup p q x xs (⟦ alg , coh ⟧ xs) i
\end{code}
%</elim-runner>
\begin{code}
⟦ alg ⟧ (trunc xs ys p q i j)  =
  isOfHLevel→isOfHLevelDep 2
    (alg .snd .c-set)
    (⟦ alg ⟧ xs) (⟦ alg ⟧ ys)
    (cong ⟦ alg ⟧ p) (cong ⟦ alg ⟧ q)
    (trunc xs ys p q)
    i j

open import Data.Maybe
open import Data.Maybe.Properties
open import Path.Reasoning
open import Relation.Nullary.Discrete.Properties

\end{code}
%<*min-funcs>
\begin{code}
⋀ : Φ A (Maybe 𝑀)
⋀ .fst (w ◃ x ∷ xs ⟨ nothing  ⟩) = just w
⋀ .fst (w ◃ x ∷ xs ⟨ just m   ⟩) = just (w ⊓ m)
⋀ .fst [] = nothing
\end{code}
%</min-funcs>
%<*min-proofs>
\begin{code}
⋀ .snd .c-dup p q _ _ nothing = refl
⋀ .snd .c-dup p q _ _ (just r) = cong just (
  p ⊓ (q ⊓ r) ≡˘⟨ ⊓-assoc p q r ⟩
  (p ⊓ q) ⊓ r ∎)
⋀ .snd .c-com p _ q _ _ nothing = cong just (
  p ⊓ q ≡⟨ ⊓-comm p q ⟩
  q ⊓ p ∎)
⋀ .snd .c-com p _ q _ _ (just r) = cong just (
  p ⊓ (q ⊓ r)  ≡˘⟨ ⊓-assoc p q r ⟩
  (p ⊓ q) ⊓ r  ≡⟨ cong (_⊓ r) (⊓-comm p q) ⟩
  (q ⊓ p) ⊓ r  ≡⟨ ⊓-assoc q p r ⟩
  q ⊓ (p ⊓ r) ∎)
\end{code}
%</min-proofs>
\begin{code}
⋀ .snd .c-set _ = Discrete→isSet (discreteMaybe _≟_)
\end{code}
\begin{code}
postulate
  _∪_ : S A → S A → S A

\end{code}
%<*delay>
\begin{code}
_⋊ : 𝑀 → Φ A (S A)
(_   ⋊) .fst [] = []
(w₁  ⋊) .fst (w₂ ◃ x ∷ _ ⟨ xs ⟩) =
  w₁ ∙ w₂ ◃ x ∷ xs
\end{code}
%</delay>
\begin{code}
(w₁ ⋊) .snd .c-set _ = trunc
(w₁ ⋊) .snd .c-dup p q x xs P⟨xs⟩ =
  w₁ ∙ p ◃ x ∷ w₁ ∙ q ◃ x ∷ P⟨xs⟩ ≡⟨ dup (w₁ ∙ p) (w₁ ∙ q) x P⟨xs⟩ ⟩
  ((w₁ ∙ p) ⊓ (w₁ ∙ q)) ◃ x ∷ P⟨xs⟩ ≡˘⟨ cong (_◃ x ∷ P⟨xs⟩) (∙-distribʳ-⊓ w₁ p q) ⟩
  w₁ ∙ (p ⊓ q) ◃ x ∷ P⟨xs⟩ ∎
(w₁ ⋊) .snd .c-com p x q y xs P⟨xs⟩ = com (w₁ ∙ p) x (w₁ ∙ q) y P⟨xs⟩
\end{code}
%<*bind>
\begin{code}
bind : (A → S B) → Φ A (S B)
bind k .fst [] = []
bind k .fst (w ◃ x ∷ _ ⟨ ys ⟩) =
  ⟦ w ⋊ ⟧ (k x) ∪ ys
\end{code}
%</bind>
\begin{code}
bind k .snd = {!!}

\end{code}
%<*pure>
\begin{code}
pure : A → S A
pure x = ε ◃ x ∷ []
\end{code}
%</pure>
