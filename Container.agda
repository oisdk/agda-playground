{-# OPTIONS --safe --cubical #-}

module Container where

open import Prelude

Container : Type₁
Container = Σ[ Shape ⦂ Type ] × (Shape → Type)

⟦_⟧ : ∀ {ℓ} → Container → Type ℓ → Type ℓ
⟦ S , P ⟧ X = Σ[ s ⦂ S ] × (P s → X)

cmap : {C : Container} → (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
cmap f xs = xs .fst , λ i → f (xs .snd i)
