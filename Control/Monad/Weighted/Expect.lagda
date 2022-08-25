\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Algebra
open import HLevels
open import Level

module Control.Monad.Weighted.Expect {ℓ} {𝑅 : Type ℓ} (rng : Semiring 𝑅) (cIsSet : isSet 𝑅) where

open Semiring rng renaming (+-comm to +-com)

open import Level
open import Path
open import Path.Reasoning
open import Data.Sigma

open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Functor rng
open import Control.Monad.Weighted.Functor.TypeDef
open import Function
open import Data.Lift
open import HITs.PropositionalTruncation
open import Data.Sum

-- member-at : {A : Type a} → 𝑅 → A →  Weighted A → Type (a ℓ⊔ ℓ)
-- member-at {a = a} {A = A} w x xs = fst (⟦ alg x ⟧ xs w)
--   where
--   alg : A → Ψ[ xs ⦂ A ] (𝑅 → hProp (a ℓ⊔ ℓ))
--   alg x .fst [] w = Lift (ℓ ℓ⊔ a) (w ≡ 0#) , {!!}
--   alg x .fst (q ◃ y ∷ xs ⟨ P⟨xs⟩ ⟩) w =
--     ∥ ((x ≡ y) × ∃ p × (w ≡ p + q) × fst (P⟨xs⟩ p)) ⊎ ((x ≢ y) × fst (P⟨xs⟩ w)) ∥ , squash
--   alg x .snd .c-set = {!!}
--   alg x .snd .c-dup p q y xs ψ⟨xs⟩ = funExt λ w → {!!}
--   alg x .snd .c-com p y q z xs ψ⟨xs⟩ = funExt λ w → {!!}
--   alg x .snd .c-del y xs ψ⟨xs⟩ = funExt λ w → {!!}




\end{code}
%<*expect-alg>
\begin{code}
∫ : (A → 𝑅) → Φ A 𝑅
∫ f .fst (p ◃ x ∷ _ ⟨ ∫fxs ⟩)  = p * f x + ∫fxs
∫ f .fst []                    = 0#
\end{code}
%</expect-alg>
%<*com>
\begin{code}
∫ f .snd .c-com p x q y _ r =
  p * f x + (q * f y + r)
    ≡˘⟨ +-assoc _ _ r ⟩
  p * f x + q * f y + r
    ≡⟨ cong (_+ r) (+-com _ _) ⟩
  q * f y + p * f x + r
    ≡⟨ +-assoc _ _ r ⟩
  q * f y + (p * f x + r) ∎
\end{code}
%</com>
%<*dup>
\begin{code}
∫ f .snd .c-dup p q x _ r =
  p * f x + (q * f x + r)
    ≡˘⟨ +-assoc _ _ r ⟩
  (p * f x + q * f x) + r
    ≡˘⟨ cong (_+ r) (⟨+⟩* _ _ _) ⟩
  (p + q) * f x + r ∎
\end{code}
%</dup>
%<*del>
\begin{code}
∫ f .snd .c-del x _ r =
  0# * f x + r
    ≡⟨ cong (_+ r) (0* (f x)) ⟩
  0# + r
    ≡⟨ 0+ r ⟩
  r ∎
\end{code}
%</del>
\begin{code}
∫ f .snd .c-set _ = cIsSet

expect : (A → 𝑅) → Weighted A → 𝑅
expect f xs = ⟦ ∫ f ⟧ xs

syntax expect (λ x → e) = ∫ e 𝑑 x


open import Algebra.SemiringLiterals rng
open import Data.Nat hiding (_+_; _*_)
open import Data.Unit
open import Data.Nat.Literals
open import Literals.Number

_/_ : 𝑅 → 𝑅 → 𝑅
x / y = x
⅙ : 𝑅
⅙ = 1#


die : Weighted ℕ
\end{code}
%<*die>
\begin{code}
die = ⅙ ◃ 1 ∷ ⅙ ◃ 2 ∷ ⅙ ◃ 3 ∷ ⅙ ◃ 4 ∷ ⅙ ◃ 5 ∷ ⅙ ◃ 6 ∷ []
\end{code}
%</die>
\begin{code}


open import Data.Bool
open import Agda.Builtin.Nat using (_<_)
open import Algebra.SemiringLiterals
open import Data.Unit.UniversePolymorphic

ℙ[3<] : 𝑅
\end{code}
%<*p-3>
\begin{code}
ℙ[3<] = (∫ if 3 < x then 1 else 0 𝑑 x) die
\end{code}
%</p-3>
\begin{code}
open import Control.Monad.Weighted.Union rng
\end{code}
%<*int-distrib>
\begin{code}
∫-distrib : ∀ (f : A → 𝑅) (ys : Weighted A) → Ψ[ xs ⦂ A ] ⟦ ∫ f ⟧ xs + ⟦ ∫ f ⟧ ys ≡ ⟦ ∫ f ⟧ (xs ∪ ys)
∫-distrib f ys .fst [] = 0+ (⟦ ∫ f ⟧ ys)
∫-distrib f ys .fst (w ◃ x ∷ xs ⟨ P⟨xs⟩ ⟩) =
  ⟦ ∫ f ⟧ (w ◃ x ∷ xs) + ⟦ ∫ f ⟧ ys    ≡⟨⟩
  (w * f x + ⟦ ∫ f ⟧ xs) + ⟦ ∫ f ⟧ ys  ≡⟨ +-assoc _ _ _ ⟩
  w * f x + (⟦ ∫ f ⟧ xs + ⟦ ∫ f ⟧ ys)  ≡⟨ cong (w * f x +_) P⟨xs⟩ ⟩
  w * f x + ⟦ ∫ f ⟧ (xs ∪ ys)          ≡⟨⟩
  ⟦ ∫ f ⟧ (w ◃ x ∷ xs ∪ ys) ∎
∫-distrib f ys .snd = prop-coh λ _ → cIsSet _ _
\end{code}
%</int-distrib>
