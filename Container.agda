{-# OPTIONS --safe --cubical #-}

module Container where

open import Prelude

Container : (s p : Level) → Type (ℓsuc (s ℓ⊔ p))
Container s p = Σ[ Shape ⦂ Type s ] × (Shape → Type p)

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ℓ⊔ p ℓ⊔ ℓ)
⟦ S , P ⟧ X = Σ[ s ⦂ S ] × (P s → X)

cmap : ∀ {s p} {C : Container s p} → (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
cmap f xs = xs .fst , λ i → f (xs .snd i)
{-# INLINE cmap #-}
