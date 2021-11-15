{-# OPTIONS --no-positivity-check #-}

open import Algebra
open import Algebra.Monus
open import Prelude

module Codata.SegFix
  {ℓ}
  (mon : CommutativeMonoid ℓ)
  (𝐹 : CommutativeMonoid.𝑆 mon → Type ℓ → Type ℓ)
  (functor : ∀ {s} → IsFunctor (𝐹 s))
  where

open POM (algebraic-pom mon)
module _ {s : 𝑆} where
  open IsFunctor (functor {s = s}) public renaming (map to fmap)

mutual
  data Fix″ (w : 𝑆) (i : 𝑆) : Type ℓ where
    coacc : ((w≤i : w ≤ i) → 𝐹 w (Fix′ (fst w≤i))) → Fix″ w i

  Fix′ : 𝑆 → Type ℓ
  Fix′ i = ∃ w × Fix″ w i

Fix : 𝑆 → Type ℓ
Fix w = 𝐹 w (∀ {i} → Fix′ i)

module _
    (B : Type ℓ)
    (ϕ : B → ∃ w × (w ≢ ε) × (𝐹 w B))
    where
    unfold′ : ∀ {i} → Acc _≺_ i → B → Fix′ i
    unfold′ a = map₂ coacc ∘ map₂ (λ { {u} (w≢ε , r) (_ , i≡u∙k) → fmap (case a of λ { (acc wf) → unfold′ (wf _ (u , i≡u∙k ; comm _ _  , w≢ε))  }) r}) ∘ ϕ


module _
  (wellFounded : WellFounded _≺_)
  (B : 𝑆 → Type ℓ)
  (ϕ : ∀ {w} → B w → 𝐹 w (∃ v × (v ≢ ε) × B v))
  where

  unfold : ∀ {w} → B w → Fix w
  unfold = fmap (λ r {i} → unfold′ _ (map₂ (map₂ ϕ)) (wellFounded _) r) ∘ ϕ
