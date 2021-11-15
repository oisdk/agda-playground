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


-- mutual
--   Fix′ : 𝑆 → Type ℓ
--   Fix′ i = ∃ w × FixF w i

--   FixF : 𝑆 → 𝑆 → Type ℓ
--   FixF w i = 𝐹 w (FixF′ w i)

data Fix′ (i : 𝑆) : Type ℓ where
  _◃_ : ∀ w → ((w≤i : w ≤ i) → 𝐹 w (Fix′ (fst w≤i))) → Fix′ i

Fix : 𝑆 → Type ℓ
Fix w = 𝐹 w (∀ {i} → Fix′ i)

module _
    (B : 𝑆 → Type ℓ) -- The seed type
    (ϕ : ∀ {i} → -- At depth i
           B i → -- With this seed
           ∃ w × (w ≢ ε) × ((w≤i : w ≤ i) → 𝐹 w (B (fst w≤i)))
           )
    where
    mutual
      unfold′ : ∀ {i} → Acc _≺_ i → B i → Fix′ i
      unfold′ a = uncurry _◃_ ∘ map₂ (λ { {u} (w≢ε , r) w≤i → fmap (case a of λ { (acc wf) → unfold′ (wf _ (u , snd w≤i ; comm _ _  , w≢ε))  }) (r w≤i)} ) ∘ ϕ
