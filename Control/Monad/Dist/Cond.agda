{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Dist.Cond {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Control.Monad.Dist.Definition rng
open import Control.Monad.Dist.Eliminators rng
open import Control.Monad.Dist.Union rng

cond-alg : 𝑅 → W-ϕ[ A ] W A
[ cond-alg c ]-set = trunc
[ cond-alg c ] p & x ∷ _ ⟨ pxs ⟩ = c * p & x ∷ pxs
[ cond-alg c ][] = []
[ cond-alg c ]-com p x q y _ pxs = com (c * p) x (c * q) y pxs
[ cond-alg p ]-dup q r x _ xs =
  p * q & x ∷ p * r & x ∷ xs ≡⟨ dup (p * q) (p * r) x xs ⟩
  p * q + p * r & x ∷ xs     ≡˘⟨ cong (_& x ∷ xs) (*⟨+⟩ p q r) ⟩
  p * (q + r) & x ∷ xs       ∎
[ cond-alg p ]-del x _ xs =
  p * 0# & x ∷ xs ≡⟨ cong (_& x ∷ xs) (*0 p) ⟩
  0# & x ∷ xs     ≡⟨ del x xs ⟩
  xs              ∎

infixr 5 _⋊_
_⋊_ : 𝑅 → W A → W A
x ⋊ xs = cond-alg x ↓ xs

⋊-distribʳ : ∀ p q → (xs : W A) → (p ⋊ xs) ∪ (q ⋊ xs) ≡ p + q ⋊ xs
⋊-distribʳ p q xs = ⋊-distribʳ′ p q ⇓≡ xs
  where
  ⋊-distribʳ′ : ∀ p q → W-ψ[ xs ⦂ A ]≡ (p ⋊ xs) ∪ (q ⋊ xs) ⊜ (p + q) ⋊ xs
  ⟦ ⋊-distribʳ′ p q ⟧≡[] = refl
  ⟦ ⋊-distribʳ′ p q ⟧≡ r & x ∷ xs ⟨ P ⟩ =
    (p ⋊ r & x ∷ xs) ∪ (q ⋊ r & x ∷ xs)   ≡˘⟨ ∪-cons (q * r) x (p ⋊ r & x ∷ xs) (q ⋊ xs)  ⟩
    q * r & x ∷ (p ⋊ r & x ∷ xs) ∪ q ⋊ xs ≡⟨ cong (_∪ q ⋊ xs) (dup (q * r) (p * r) x (p ⋊ xs)) ⟩
    q * r + p * r & x ∷ (p ⋊ xs) ∪ q ⋊ xs ≡˘⟨ cong (_& x ∷ ((p ⋊ xs) ∪ (q ⋊ xs))) (⟨+⟩* q p r) ⟩
    (q + p) * r & x ∷ (p ⋊ xs) ∪ (q ⋊ xs) ≡⟨ cong ((q + p) * r & x ∷_) P ⟩
    (q + p) * r & x ∷ (p + q) ⋊ xs        ≡⟨ cong (λ pq → pq * r & x ∷ (p + q) ⋊ xs) (+-comm q p) ⟩
    (p + q) * r & x ∷ (p + q) ⋊ xs        ≡⟨⟩
    (p + q) ⋊ (r & x ∷ xs) ∎

⋊-distribˡ : ∀ p → (xs ys : W A) → (p ⋊ xs) ∪ (p ⋊ ys) ≡ p ⋊ (xs ∪ ys)
⋊-distribˡ = λ p xs ys → ⋊-distribˡ′ p ys ⇓≡ xs
  module JDistribL where
  ⋊-distribˡ′ : ∀ p ys → W-ψ[ xs ⦂ A ]≡ (p ⋊ xs) ∪ (p ⋊ ys) ⊜ p ⋊ (xs ∪ ys)
  ⟦ ⋊-distribˡ′ p ys ⟧≡[] = refl
  ⟦ ⋊-distribˡ′ p ys ⟧≡ q & x ∷ xs ⟨ P ⟩ = cong (p * q & x ∷_) P

0⋊ : (xs : W A) → 0# ⋊ xs ≡ []
0⋊ xs = 0⋊′ ⇓≡ xs
  where
  0⋊′ : W-ψ[ xs ⦂ A ]≡ 0# ⋊ xs ⊜ []
  ⟦ 0⋊′ ⟧≡[] = refl
  ⟦ 0⋊′ ⟧≡ p & x ∷ xs ⟨ P ⟩ =
    0# ⋊ (p & x ∷ xs)    ≡⟨⟩
    0# * p & x ∷ 0# ⋊ xs ≡⟨ cong (_& x ∷ 0# ⋊ xs) (0* p) ⟩
    0# & x ∷ 0# ⋊ xs     ≡⟨ del x (0# ⋊ xs) ⟩
    0# ⋊ xs              ≡⟨ P ⟩
    [] ∎
