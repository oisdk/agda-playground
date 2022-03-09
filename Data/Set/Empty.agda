module Data.Set.Empty where

open import Prelude
open import Data.Set.Eliminators
open import Data.Set.Definition
open import Data.Bool.Properties

null-alg : ψ A Bool
null-alg .fst ∅ = true
null-alg .fst (_ ∷ _ ⟨ _ ⟩) = false
null-alg .snd .c-trunc _ = isSetBool
null-alg .snd .c-com _ _ _ _ = refl
null-alg .snd .c-dup _ _ _ = refl

null : 𝒦 A → Bool
null = ⟦ null-alg ⟧

Empty : 𝒦 A → Type
Empty = T ∘ null

Empty? : (xs : 𝒦 A) → Dec (Empty xs)
Empty? = T? ∘ null

∅≢∷ : ∀ {x : A} {xs} → ∅ ≢ x ∷ xs
∅≢∷ = true≢false ∘ cong null
