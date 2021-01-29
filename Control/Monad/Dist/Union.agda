{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Dist.Union {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import HLevels
open import Control.Monad.Dist.Definition rng
open import Control.Monad.Dist.Eliminators rng

union-alg : W A → W-ϕ[ A ] W A
[ union-alg ys ]-set = trunc
[ union-alg ys ] p & x ∷ _ ⟨ pxs ⟩ = p & x ∷ pxs
[ union-alg ys ][] = ys
[ union-alg ys ]-dup p q x _ pxs = dup p q x pxs
[ union-alg ys ]-com p x q y _ pxs = com p x q y pxs
[ union-alg ys ]-del x _ pxs = del x pxs

infixr 5 _∪_
_∪_ : W A → W A → W A
xs ∪ ys = union-alg ys ↓ xs

∪-assoc : (xs ys zs : W A) → xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs
∪-assoc xs ys zs = ∪-assoc′ ys zs ⇓≡ xs
  where
  ∪-assoc′ : ∀ ys zs → W-ψ[ xs ⦂ A ]≡ xs ∪ (ys ∪ zs) ⊜ (xs ∪ ys) ∪ zs
  ⟦ ∪-assoc′ ys zs ⟧≡[] = refl
  ⟦ ∪-assoc′ ys zs ⟧≡ p & x ∷ xs ⟨ P ⟩ = cong (p & x ∷_) P

∪-idr : (xs : W A) → xs ∪ [] ≡ xs
∪-idr xs = ∪-idr′ ⇓≡ xs
  where
  ∪-idr′ : W-ψ[ xs ⦂ A ]≡ xs ∪ [] ⊜ xs
  ⟦ ∪-idr′ ⟧≡ p & x ∷ xs ⟨ Pxs ⟩ = cong (p & x ∷_) Pxs
  ⟦ ∪-idr′ ⟧≡[] = refl

∪-cons : ∀ p x (xs ys : W A) → p & x ∷ xs ∪ ys ≡ xs ∪ p & x ∷ ys
∪-cons p x xs ys = ∪-cons′ p x ys ⇓≡ xs
  where
  ∪-cons′ : ∀ p x ys → W-ψ[ xs ⦂ A ]≡ p & x ∷ xs ∪ ys ⊜ xs ∪ p & x ∷ ys
  ⟦ ∪-cons′ p x ys ⟧≡ q & y ∷ xs ⟨ Pxs ⟩ = com p x q y (xs ∪ ys) ; cong (q & y ∷_) Pxs
  ⟦ ∪-cons′ p x ys ⟧≡[] = refl

∪-com : (xs ys : W A) → xs ∪ ys ≡ ys ∪ xs
∪-com xs ys = ∪-com′ ys ⇓≡ xs
  where
  ∪-com′ : ∀ ys → W-ψ[ xs ⦂ A ]≡ xs ∪ ys ⊜ ys ∪ xs
  ⟦ ∪-com′ ys ⟧≡ p & x ∷ xs ⟨ Pxs ⟩ = cong (p & x ∷_) Pxs ; ∪-cons p x ys xs
  ⟦ ∪-com′ ys ⟧≡[] = sym (∪-idr ys)
