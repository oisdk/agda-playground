{-# OPTIONS --no-positivity-check #-}

open import Algebra
open import Algebra.Monus
open import Prelude

module Codata.SegFix
  {ℓ}
  (mon : CommutativeMonoid ℓ)
  (𝐹 : CommutativeMonoid.𝑆 mon → Type ℓ → Type ℓ)
  (functor : ∀ {s} → Functor (𝐹 s))
  where

open POM (algebraic-pom mon)
module _ {s : 𝑆} where
  open Functor (functor {s = s}) public renaming (map to fmap)

private variable i j k : 𝑆

mutual
  data Fix″ (i : 𝑆) (j : 𝑆) : Type ℓ where
    coacc : ((i≤j : i ≤ j) → 𝐹 i (Fix′ (fst i≤j))) → Fix″ i j

  Fix′ : 𝑆 → Type ℓ
  Fix′ i = ∃ j × Fix″ j i

Fix : 𝑆 → Type ℓ
Fix i = 𝐹 i (∀ {j} → Fix′ j)

module _
    (B : Type ℓ)
    (ϕ : B → ∃ i × (i ≢ ε) × 𝐹 i B)
    where
    mutual
      unfold′ : Acc _≺_ i → B → Fix′ i
      unfold′ a = map₂ (coacc ∘ unfold″ a) ∘ ϕ

      unfold″ : Acc _≺_ i → (j ≢ ε) × 𝐹 j B → (j≤i : j ≤ i) → 𝐹 j (Fix′ (fst j≤i))
      unfold″ a (j≢ε , r) (k , i≡j∙k) = fmap (unfold‴ a (_ , i≡j∙k ; comm _ k , j≢ε)) r

      unfold‴ : Acc _≺_ i → j ≺ i → B → Fix′ j
      unfold‴ (acc wf) j≺i = unfold′ (wf _ j≺i)

module _
  (wellFounded : WellFounded _≺_)
  (B : 𝑆 → Type ℓ)
  (ϕ : ∀ {w} → B w → 𝐹 w (∃ v × (v ≢ ε) × B v))
  where
  unfold : ∀ {w} → B w → Fix w
  unfold = fmap (λ r {i} → unfold′ _ (map₂ (map₂ ϕ)) (wellFounded _) r) ∘ ϕ
