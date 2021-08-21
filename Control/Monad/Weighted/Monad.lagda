\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Weighted.Monad {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Data.Sigma

open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Union rng
open import Control.Monad.Weighted.Cond rng
open import Control.Monad.Weighted.Functor rng
open import Control.Monad.Weighted.Functor.TypeDef
\end{code}
%<*bind-alg>
\begin{code}
bind-alg :  (A → Weighted B) →
            Φ A (Weighted B)
bind-alg f .fst (p ◃ x ∷ _ ⟨ xs ⟩) = (p ⋊ f x) ∪ xs
bind-alg f .fst [] = []
\end{code}
%</bind-alg>
\begin{code}
bind-alg f .snd .c-set _ = trunc
bind-alg f .snd .c-del x _ xs = cong (_∪ xs) (0⋊ (f x))
bind-alg f .snd .c-dup p q x _ xs =
  p ⋊ f x ∪ (q ⋊ f x ∪ xs)  ≡⟨ ∪-assoc (p ⋊ f x) (q ⋊ f x) xs ⟩
  (p ⋊ f x ∪ q ⋊ f x) ∪ xs  ≡⟨ cong (_∪ xs) (⋊-distribʳ p q (f x)) ⟩
  (p + q ⋊ f x) ∪ xs ∎
bind-alg f .snd .c-com p x q y _ xs =
  p ⋊ f x ∪ q ⋊ f y ∪ xs    ≡⟨ ∪-assoc (p ⋊ f x) (q ⋊ f y) xs ⟩
  (p ⋊ f x ∪ q ⋊ f y) ∪ xs  ≡⟨ cong (_∪ xs) (∪-com (p ⋊ f x) (q ⋊ f y)) ⟩
  (q ⋊ f y ∪ p ⋊ f x) ∪ xs  ≡˘⟨ ∪-assoc (q ⋊ f y) (p ⋊ f x) xs ⟩
  q ⋊ f y ∪ p ⋊ f x ∪ xs ∎
\end{code}
%<*bind-impl>
\begin{code}
_>>=_ :  Weighted A → (A → Weighted B) →
         Weighted B
xs >>= f = ⟦ bind-alg f ⟧ xs
\end{code}
%</bind-impl>
%<*pure>
\begin{code}
pure : A → Weighted A
pure x = 1# ◃ x ∷ []
\end{code}
%</pure>
\begin{code}
_>>_ : Weighted A → Weighted B → Weighted B
xs >> ys = do
  _ ← xs
  ys

_<*>_ : Weighted (A → B) → Weighted A → Weighted B
fs <*> xs = do
  f ← fs
  x ← xs
  pure (f x)

>>=-distrib : (xs ys : Weighted A) (g : A → Weighted B) → (xs ∪ ys) >>= g ≡ (xs >>= g) ∪ (ys >>= g)
>>=-distrib xs ys g = ⟦ >>=-distrib′ ys g ⟧ xs
  where
  >>=-distrib′ : (ys : Weighted A) (g : A → Weighted B) → Ψ[ xs ⦂ A ] ((xs ∪ ys) >>= g) ≡ (xs >>= g) ∪ (ys >>= g)
  >>=-distrib′ ys g .fst [] = refl
  >>=-distrib′ ys g .fst (p ◃ x ∷ xs ⟨ P ⟩) =
    (((p ◃ x ∷ xs) ∪ ys) >>= g)          ≡⟨⟩
    (p ◃ x ∷ xs ∪ ys) >>= g              ≡⟨⟩
    p ⋊ g x ∪ ((xs ∪ ys) >>= g)          ≡⟨ cong (p ⋊ g x ∪_) P ⟩
    p ⋊ g x ∪ ((xs >>= g) ∪ (ys >>= g))  ≡⟨ ∪-assoc (p ⋊ g x) (xs >>= g) (ys >>= g) ⟩
    (p ⋊ g x ∪ (xs >>= g)) ∪ (ys >>= g)  ≡⟨⟩
    ((p ◃ x ∷ xs) >>= g) ∪ (ys >>= g) ∎
  >>=-distrib′ ys g .snd = eq-coh

⋊-assoc->>= : ∀ p (xs : Weighted A) (f : A → Weighted B) → (p ⋊ xs) >>= f ≡ p ⋊ (xs >>= f)
⋊-assoc->>= p xs f = ⟦ ⋊-assoc->>=′ p f ⟧ xs
  where
  ⋊-assoc->>=′ : ∀ p (f : A → Weighted B) → Ψ[ xs ⦂ A ] (p ⋊ xs) >>= f ≡ p ⋊ (xs >>= f)
  ⋊-assoc->>=′ p f .fst [] = refl
  ⋊-assoc->>=′ p f .fst (q ◃ x ∷ xs ⟨ P ⟩) =
    (p ⋊ (q ◃ x ∷ xs)) >>= f            ≡⟨⟩
    (p * q ◃ x ∷ p ⋊ xs) >>= f          ≡⟨⟩
    ((p * q) ⋊ f x) ∪ ((p ⋊ xs) >>= f)  ≡⟨ cong (((p * q) ⋊ f x) ∪_) P ⟩
    ((p * q) ⋊ f x) ∪ (p ⋊ (xs >>= f))  ≡⟨ cong (_∪ (p ⋊ (xs >>= f))) (*-assoc-⋊ p q (f x)) ⟩
    (p ⋊ (q ⋊ f x)) ∪ (p ⋊ (xs >>= f))  ≡⟨ ⋊-distribˡ p (q ⋊ f x) (xs >>= f) ⟩
    p ⋊ ((q ◃ x ∷ xs) >>= f) ∎
  ⋊-assoc->>=′ p f .snd = eq-coh

>>=-idˡ : (x : A) → (f : A → Weighted B)
      → (pure x >>= f) ≡ f x
>>=-idˡ x f =
  pure x >>= f         ≡⟨⟩
  (1# ◃ x ∷ []) >>= f  ≡⟨⟩
  1# ⋊ f x ∪ [] >>= f  ≡⟨⟩
  1# ⋊ f x ∪ []        ≡⟨ ∪-idr (1# ⋊ f x) ⟩
  1# ⋊ f x             ≡⟨ 1⋊ (f x) ⟩
  f x ∎

>>=-idʳ : (xs : Weighted A) → xs >>= pure ≡ xs
>>=-idʳ = ⟦ >>=-idʳ′ ⟧
  where
  >>=-idʳ′ : Ψ[ xs ⦂ A ] xs >>= pure ≡ xs
  >>=-idʳ′ .fst [] = refl
  >>=-idʳ′ .fst (p ◃ x ∷ xs ⟨ P ⟩) =
    ((p ◃ x ∷ xs) >>= pure) ≡⟨⟩
    p ⋊ (pure x) ∪ (xs >>= pure) ≡⟨⟩
    p ⋊ (1# ◃ x ∷ []) ∪ (xs >>= pure) ≡⟨⟩
    p * 1# ◃ x ∷ [] ∪ (xs >>= pure) ≡⟨⟩
    p * 1# ◃ x ∷ (xs >>= pure) ≡⟨ cong (_◃ x ∷ (xs >>= pure)) (*1 p) ⟩
    p ◃ x ∷ xs >>= pure ≡⟨ cong (p ◃ x ∷_) P ⟩
    p ◃ x ∷ xs ∎
  >>=-idʳ′ .snd = eq-coh

>>=-assoc : (xs : Weighted A) → (f : A → Weighted B) → (g : B → Weighted C)
      → ((xs >>= f) >>= g) ≡ xs >>= (λ x → f x >>= g)
>>=-assoc xs f g = ⟦ >>=-assoc′ f g ⟧ xs
  where
  >>=-assoc′ : (f : A → Weighted B) → (g : B → Weighted C) → Ψ[ xs ⦂ A ] ((xs >>= f) >>= g) ≡ xs >>= (λ x → f x >>= g)
  >>=-assoc′ f g .fst [] = refl
  >>=-assoc′ f g .fst (p ◃ x ∷ xs ⟨ P ⟩) =
    (((p ◃ x ∷ xs) >>= f) >>= g) ≡⟨⟩
    ((p ⋊ f x ∪ (xs >>= f)) >>= g) ≡⟨ >>=-distrib (p ⋊ f x) (xs >>= f) g ⟩
    ((p ⋊ f x) >>= g) ∪ ((xs >>= f) >>= g) ≡⟨ cong ((p ⋊ f x) >>= g ∪_) P ⟩
    ((p ⋊ f x) >>= g) ∪ (xs >>= (λ y → f y >>= g)) ≡⟨ cong (_∪ (xs >>= (λ y → f y >>= g))) (⋊-assoc->>= p (f x) g) ⟩
    p ⋊ (f x >>= g) ∪ (xs >>= (λ y → f y >>= g)) ≡⟨⟩
    ((p ◃ x ∷ xs) >>= (λ y → f y >>= g)) ∎
  >>=-assoc′ f g .snd = eq-coh
\end{code}
