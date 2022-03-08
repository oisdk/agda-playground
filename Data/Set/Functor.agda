module Data.Set.Functor where

open import Prelude
open import Data.Set.Definition
open import Data.Set.Eliminators
open import Algebra

smap : (A → B) → 𝒦 A → 𝒦 B
smap f = ⟦ alg f ⟧
  where
  alg : (A → B) → ψ A (𝒦 B)
  alg f .fst ∅ = ∅
  alg f .fst (x ∷ _ ⟨ xs ⟩) = f x ∷ xs
  alg f .snd .c-trunc _ = trunc
  alg f .snd .c-com x y xs P⟨xs⟩ = com (f x) (f y) P⟨xs⟩
  alg f .snd .c-dup x xs P⟨xs⟩ = dup (f x) P⟨xs⟩

smap-id : (xs : 𝒦 A) → smap id xs ≡ xs
smap-id = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (smap id xs ≡ xs)
  alg .fst ∅ = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) i = x ∷ P⟨xs⟩ i
  alg .snd = prop-coh λ _ → trunc _ _

smap-comp : (f : B → C) (g : A → B) (x : 𝒦 A) →
      smap (f ∘ g) x ≡ smap f (smap g x)
smap-comp f g = ⟦ alg f g ⟧
  where
  alg : (f : B → C) (g : A → B) → Ψ[ xs ⦂ 𝒦 A ] ↦ (smap (f ∘ g) xs ≡ smap f (smap g xs))
  alg f g .snd = prop-coh λ _ → trunc _ _
  alg f g .fst ∅ = refl
  alg f g .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) i = f (g x) ∷ P⟨xs⟩ i

-- module _ {a} where
--   functorSet : Functor a a
--   functorSet .Functor.𝐹 = 𝒦
--   functorSet .Functor.map = smap
--   functorSet .Functor.map-id = funExt smap-id
--   functorSet .Functor.map-comp = funExt smap-comp
