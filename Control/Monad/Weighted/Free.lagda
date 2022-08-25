\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Level

module Control.Monad.Weighted.Free {ℓ} {𝑅 : Type ℓ} (rng : Semiring 𝑅) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Data.Sigma
open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng renaming (⟦_⟧ to ⟦_⟧′)
open import Control.Monad.Weighted.Union rng using () renaming (_∪_ to _∪′_)
open import Control.Monad.Weighted.Cond rng using () renaming (_⋊_ to _⋊′_)
open import Control.Monad.Weighted.Semimodule rng
open import Control.Monad.Weighted.Functor.TypeDef
open import Control.Monad.Weighted.Functor

inj : A → Weighted A
inj x = 1# ◃ x ∷ []

module Proof {ℓ} {𝑀 : Type ℓ} (mod : LeftSemimodule rng 𝑀) (vIsSet : isSet 𝑀) where
  module Mod = LeftSemimodule mod
  open Mod using (_⋊_; _∪_; ∅)
\end{code}
%<*hom>
\begin{code}
  hom : (A → 𝑀) → Φ A 𝑀
  hom h .fst (p ◃ x ∷ _ ⟨ xs ⟩) = (p ⋊ h x) ∪ xs
  hom h .fst [] = ∅
\end{code}
%</hom>
\begin{code}
  hom h .snd .c-set _ = vIsSet
  hom h .snd .c-dup p q x _ xs =
    p ⋊ h x ∪ (q ⋊ h x ∪ xs) ≡˘⟨ Mod.∪-assoc _ _ _ ⟩
    (p ⋊ h x ∪ q ⋊ h x) ∪ xs ≡˘⟨ cong (_∪ xs) (Mod.⟨+⟩⋊ p q (h x)) ⟩
    (p + q) ⋊ h x ∪ xs ∎
  hom h .snd .c-com p x q y _ xs =
    p ⋊ h x ∪ (q ⋊ h y ∪ xs) ≡˘⟨ Mod.∪-assoc _ _ _ ⟩
    (p ⋊ h x ∪ q ⋊ h y) ∪ xs ≡⟨ cong (_∪ xs) (Mod.comm _ _) ⟩
    (q ⋊ h y ∪ p ⋊ h x) ∪ xs ≡⟨ Mod.∪-assoc _ _ _ ⟩
    q ⋊ h y ∪ (p ⋊ h x ∪ xs) ∎
  hom h .snd .c-del x _ xs =
    0# ⋊ h x ∪ xs ≡⟨ cong (_∪ xs) (Mod.0⋊ _) ⟩
    ∅ ∪ xs ≡⟨ Mod.∅∪ xs ⟩
    xs ∎

  module _ (h : A → 𝑀) where
    ⟦_⟧ : Weighted A → 𝑀
    ⟦ xs ⟧ = ⟦ hom h ⟧′ xs


    module _ (hom : SemimoduleHomomorphism[ rng ] semimodule {A = A} ⟶ mod) where
      module Hom = SemimoduleHomomorphism[_]_⟶_ hom
      open Hom using (f)

      uniq-alg : (inv : ∀ x → f (inj x) ≡ h x) → Ψ[ xs ⦂ A ] ⟦ xs ⟧ ≡ f xs
      uniq-alg inv .snd = prop-coh λ _ → vIsSet _ _
      uniq-alg inv .fst (p ◃ x ∷ xs ⟨ pxs ⟩) =
        ⟦ p ◃ x ∷ xs ⟧ ≡⟨⟩
        (p ⋊ h x) ∪ ⟦ xs ⟧ ≡˘⟨ cong (_∪ ⟦ xs ⟧) (cong (p ⋊_) (inv x)) ⟩
        p ⋊ f (inj x) ∪ ⟦ xs ⟧ ≡˘⟨ cong (_∪ ⟦ xs ⟧) (Hom.⋊-homo p _) ⟩
        f (p ⋊′ inj x) ∪ ⟦ xs ⟧ ≡⟨ cong (_∪ ⟦ xs ⟧) (cong f (cong (_◃ x ∷ []) (*1 p))) ⟩
        f (p ◃ x ∷ []) ∪ ⟦ xs ⟧ ≡⟨ cong (f (p ◃ x ∷ []) ∪_) pxs ⟩
        f (p ◃ x ∷ []) ∪ f xs ≡˘⟨ Hom.∙-homo _ _ ⟩
        f (p ◃ x ∷ xs) ∎
      uniq-alg inv .fst [] = sym Hom.ε-homo

      uniq : (inv : ∀ x → f (inj x) ≡ h x) → ∀ xs → ⟦ xs ⟧ ≡ f xs
      uniq inv = ⟦ uniq-alg inv ⟧′

    inv : ∀ x → ⟦ inj x ⟧ ≡ h x
    inv x =
      ⟦ inj x ⟧ ≡⟨⟩
      ⟦ 1# ◃ x ∷ [] ⟧ ≡⟨⟩
      (1# ⋊ h x) ∪ ∅ ≡⟨ Mod.∪∅ _ ⟩
      1# ⋊ h x ≡⟨ Mod.1⋊ _ ⟩
      h x ∎

    ∪-hom : (ys : Weighted A) → Ψ[ xs ⦂ A ] ⟦ xs ∪′ ys ⟧ ≡ ⟦ xs ⟧ ∪ ⟦ ys ⟧
    ∪-hom ys .snd = prop-coh λ _ → vIsSet _ _
    ∪-hom ys .fst (p ◃ x ∷ xs ⟨ pxs ⟩) =
      ⟦ (p ◃ x ∷ xs) ∪′ ys ⟧ ≡⟨⟩
      ⟦ p ◃ x ∷ (xs ∪′ ys) ⟧ ≡⟨⟩
      p ⋊ h x ∪ ⟦ xs ∪′ ys ⟧ ≡⟨ cong ((p ⋊ h x) ∪_) pxs ⟩
      p ⋊ h x ∪ (⟦ xs ⟧ ∪ ⟦ ys ⟧) ≡˘⟨ Mod.∪-assoc (p ⋊ h x) ⟦ xs ⟧ ⟦ ys ⟧ ⟩
      p ⋊ h x ∪ ⟦ xs ⟧ ∪ ⟦ ys ⟧ ≡⟨⟩
      ⟦ p ◃ x ∷ xs ⟧ ∪ ⟦ ys ⟧ ∎
    ∪-hom ys .fst [] = sym (Mod.∅∪ ⟦ ys ⟧)

    ⋊-hom : (r : 𝑅) → Ψ[ xs ⦂ A ] ⟦ r ⋊′ xs ⟧ ≡ r ⋊ ⟦ xs ⟧
    ⋊-hom r .snd = prop-coh λ _ → vIsSet _ _
    ⋊-hom r .fst [] = sym (Mod.⋊∅ r)
    ⋊-hom r .fst (p ◃ x ∷ xs ⟨ pxs ⟩) =
      ⟦ r ⋊′ (p ◃ x ∷ xs) ⟧ ≡⟨⟩
      ⟦ r * p ◃ x ∷ r ⋊′ xs ⟧ ≡⟨⟩
      (r * p) ⋊ h x ∪ ⟦ r ⋊′ xs ⟧ ≡⟨ cong ((r * p) ⋊ h x ∪_) pxs ⟩
      (r * p) ⋊ h x ∪ r ⋊ ⟦ xs ⟧ ≡⟨ cong (_∪ r ⋊ ⟦ xs ⟧) (Mod.⟨*⟩⋊ _ _ _) ⟩
      r ⋊ (p ⋊ h x) ∪ r ⋊ ⟦ xs ⟧ ≡˘⟨ Mod.⋊⟨∪⟩ r _ _ ⟩
      r ⋊ (p ⋊ h x ∪ ⟦ xs ⟧) ≡⟨⟩
      r ⋊ ⟦ p ◃ x ∷ xs ⟧ ∎

    hom′ : SemimoduleHomomorphism[ rng ] semimodule {A = A} ⟶ mod
    MonoidHomomorphism_⟶_.f (SemimoduleHomomorphism[_]_⟶_.mon-homo hom′) = ⟦_⟧
    MonoidHomomorphism_⟶_.∙-homo (SemimoduleHomomorphism[_]_⟶_.mon-homo hom′) x y = ⟦ ∪-hom y ⟧′ x
    MonoidHomomorphism_⟶_.ε-homo (SemimoduleHomomorphism[_]_⟶_.mon-homo hom′) = refl
    SemimoduleHomomorphism[_]_⟶_.⋊-homo hom′ r = ⟦ ⋊-hom r ⟧′
\end{code}
