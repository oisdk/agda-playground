module Container.Directed where

open import Prelude
open import Container

record Directed  (𝒞 : Container ) : Type where
  S = fst 𝒞
  P = snd 𝒞
  field
    _↓_ : ∀ s → P s → S
    ⊚ : {s : S} → P s
    _⊕_ : {s : S} → (p : P s) → P (s ↓ p) → P s

    ↓id : ∀ s → s ↓ ⊚ ≡ s
    lassoc : ∀ x y z → x ↓ (y ⊕ z) ≡ (x ↓ y) ↓ z
    ⊕idʳ : ∀ {s} (x : P s) → x ⊕ ⊚ ≡ x
    ⊕idˡ : ∀ {s} x → ⊚ ⊕ x ≡[ i ≔ P (↓id s (~ i)) ]≡ x
    rassoc :
      ∀ {s} (x : P s) (y : P (s ↓ x)) → 
        (λ z → (x ⊕ y) ⊕ z) ≡[ i ≔ (P (lassoc s x y i) → P s) ]≡ (λ z → x ⊕ (y ⊕ z))

open Directed public

DCont : Type₁
DCont = Σ Container Directed

open import Data.Fin

NEList : Container
NEList .fst = ℕ
NEList .snd n = Fin (suc n)

mutual
  _⇊′_ : ∀ s → Fin s → ℕ
  suc s ⇊′ x = s ⇊ x

  _⇊_ : ∀ s → Fin (suc s) → ℕ
  s ⇊ f0 = s
  s ⇊ fs x = s ⇊′ x

_⊕⊕_ : ∀ {s} → (p : Fin (suc s)) → Fin (suc (s ⇊ p)) → Fin (suc s)
_⊕⊕_ {s} f0 y = y
_⊕⊕_ {suc s} (fs x) y = fs (x ⊕⊕ y)

-- NEList⋆ : DCont ℓzero ℓzero
-- NEList⋆ .fst = NEList
-- NEList⋆ .snd ._↓_ = _⇊_
-- NEList⋆ .snd .⊚ = f0
-- NEList⋆ .snd ._⊕_ = _⊕⊕_
-- NEList⋆ .snd .↓id _ = refl
-- NEList⋆ .snd .lassoc = {!!}
-- NEList⋆ .snd .⊕idʳ = {!!}
-- NEList⋆ .snd .⊕idˡ _ = refl
-- NEList⋆ .snd .rassoc = {!!}
