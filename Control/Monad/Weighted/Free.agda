{-# OPTIONS --cubical --safe #-}

open import Algebra

module Control.Monad.Weighted.Free {ℓ} (rng : Semiring ℓ) where

open Semiring rng

open import Level
open import Path
open import Path.Reasoning
open import HLevels
open import Control.Monad.Weighted.Definition rng
open import Control.Monad.Weighted.Eliminators rng
open import Control.Monad.Weighted.Union rng using (_<|>_)
open import Control.Monad.Weighted.Cond rng using () renaming (_⋊_ to _⋊′_)
open import Control.Monad.Weighted.Semimodule rng

inj : A → W A
inj x = 1# & x ∷ []

module Proof {ℓ} (mod : LeftSemimodule rng ℓ) (vIsSet : isSet (LeftSemimodule.𝑉 mod)) where
  module Mod = LeftSemimodule mod
  open Mod using (_⋊_; _∪_; ∅) renaming (𝑉 to 𝑀)

  module _ (h : A → 𝑀) where
    hom-alg : W-ϕ[ A ] 𝑀
    [ hom-alg ]-set = vIsSet
    [ hom-alg ] p & x ∷ _ ⟨ xs ⟩ = (p ⋊ h x) ∪ xs
    [ hom-alg ][] = ∅

    [ hom-alg ]-dup p q x _ xs =
      p ⋊ h x ∪ (q ⋊ h x ∪ xs) ≡˘⟨ Mod.∪-assoc _ _ _ ⟩
      (p ⋊ h x ∪ q ⋊ h x) ∪ xs ≡˘⟨ cong (_∪ xs) (Mod.⟨+⟩⋊ p q (h x)) ⟩
      (p + q) ⋊ h x ∪ xs ∎
    [ hom-alg ]-com p x q y _ xs =
      p ⋊ h x ∪ (q ⋊ h y ∪ xs) ≡˘⟨ Mod.∪-assoc _ _ _ ⟩
      (p ⋊ h x ∪ q ⋊ h y) ∪ xs ≡⟨ cong (_∪ xs) (Mod.comm _ _) ⟩
      (q ⋊ h y ∪ p ⋊ h x) ∪ xs ≡⟨ Mod.∪-assoc _ _ _ ⟩
      q ⋊ h y ∪ (p ⋊ h x ∪ xs) ∎
    [ hom-alg ]-del x _ xs =
      0# ⋊ h x ∪ xs ≡⟨ cong (_∪ xs) (Mod.0⋊ _) ⟩
      ∅ ∪ xs ≡⟨ Mod.∅∪ xs ⟩
      xs ∎

    ⟦_⟧ : W A → 𝑀
    ⟦ xs ⟧ = hom-alg ↓ xs


    module _ (hom : SemimoduleHomomorphism[ rng ] semimodule {A = A} ⟶ mod) where
      module Hom = SemimoduleHomomorphism[_]_⟶_ hom
      open Hom using (f)

      uniq-alg : (inv : ∀ x → f (inj x) ≡ h x) → W-ψ[ xs ⦂ A ] ⟦ xs ⟧ ≡ f xs
      ∥ uniq-alg inv ∥-prop = vIsSet _ _
      ∥ uniq-alg inv ∥ p & x ∷ xs ⟨ pxs ⟩ =
        ⟦ p & x ∷ xs ⟧ ≡⟨⟩
        (p ⋊ h x) ∪ ⟦ xs ⟧ ≡˘⟨ cong (_∪ ⟦ xs ⟧) (cong (p ⋊_) (inv x)) ⟩
        p ⋊ f (inj x) ∪ ⟦ xs ⟧ ≡˘⟨ cong (_∪ ⟦ xs ⟧) (Hom.⋊-homo p _) ⟩
        f (p ⋊′ inj x) ∪ ⟦ xs ⟧ ≡⟨ cong (_∪ ⟦ xs ⟧) (cong f (cong (_& x ∷ []) (*1 p))) ⟩
        f (p & x ∷ []) ∪ ⟦ xs ⟧ ≡⟨ cong (f (p & x ∷ []) ∪_) pxs ⟩
        f (p & x ∷ []) ∪ f xs ≡˘⟨ Hom.∙-homo _ _ ⟩
        f (p & x ∷ xs) ∎
      ∥ uniq-alg inv ∥[] = sym Hom.ε-homo

      uniq : (inv : ∀ x → f (inj x) ≡ h x) → ∀ xs → ⟦ xs ⟧ ≡ f xs
      uniq inv = ∥ uniq-alg inv ∥⇓

    inv : ∀ x → ⟦ inj x ⟧ ≡ h x
    inv x =
      ⟦ inj x ⟧ ≡⟨⟩
      ⟦ 1# & x ∷ [] ⟧ ≡⟨⟩
      (1# ⋊ h x) ∪ ∅ ≡⟨ Mod.∪∅ _ ⟩
      1# ⋊ h x ≡⟨ Mod.1⋊ _ ⟩
      h x ∎


    -- ∪-hom-alg : (ys : W A) → W-ψ[ xs ⦂ A ] ⟦ xs <|> ys ⟧ ≡ ⟦ xs ⟧ ∪ ⟦ ys ⟧
    -- ∥ ∪-hom-alg ys ∥-prop = vIsSet _ _
    -- ∥ ∪-hom-alg ys ∥ p & x ∷ xs ⟨ pxs ⟩ = {!!}
    -- ∥ ∪-hom-alg ys ∥[] = {!!}

    -- ⋊-hom-alg : (r : 𝑅) → W-ψ[ xs ⦂ A ] ⟦ r ⋊′ xs ⟧ ≡ r ⋊ ⟦ xs ⟧
    -- ∥ ⋊-hom-alg r ∥-prop = vIsSet _ _
    -- ∥ ⋊-hom-alg r ∥ p & x ∷ xs ⟨ pxs ⟩ = {!!}
    -- ∥ ⋊-hom-alg r ∥[] = {!!}

    -- hom : SemimoduleHomomorphism[ rng ] semimodule {A = A} ⟶ mod
    -- MonoidHomomorphism_⟶_.f (SemimoduleHomomorphism[_]_⟶_.mon-homo hom) = ⟦_⟧
    -- MonoidHomomorphism_⟶_.∙-homo (SemimoduleHomomorphism[_]_⟶_.mon-homo hom) x y = ∥ ∪-hom-alg y ∥⇓ x
    -- MonoidHomomorphism_⟶_.ε-homo (SemimoduleHomomorphism[_]_⟶_.mon-homo hom) = refl
    -- SemimoduleHomomorphism[_]_⟶_.⋊-homo hom r = ∥ ⋊-hom-alg r ∥⇓
