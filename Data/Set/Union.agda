module Data.Set.Union where

open import Data.Set.Definition
open import Data.Set.Eliminators
open import Prelude
open import HLevels using (isSetΠ; isPropΠ)
open import Path.Reasoning

union-alg : ψ A (𝒦 A → 𝒦 A)
union-alg .fst ∅                  ys = ys
union-alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩)  ys = x ∷ P⟨xs⟩ ys
union-alg .snd .c-trunc _ = isSetΠ λ _ → trunc
union-alg .snd .c-com x y xs P⟨xs⟩ i ys = com x y (P⟨xs⟩ ys) i
union-alg .snd .c-dup x xs P⟨xs⟩ i ys = dup x (P⟨xs⟩ ys) i

infixr 5 _∪_
_∪_ : 𝒦 A → 𝒦 A → 𝒦 A
_∪_ = ⟦ union-alg ⟧

∷-distrib : ∀ (x : A) xs ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys)
∷-distrib x = ⟦ alg x ⟧
  where
  alg : ∀ x → Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → x ∷ (xs ∪ ys) ≡ xs ∪ (x ∷ ys))
  alg x .fst ∅ ys = refl
  alg x .fst (y ∷ xs ⟨ P⟨xs⟩ ⟩) ys = com x y (xs ∪ ys) ; cong (y ∷_) (P⟨xs⟩ ys)
  alg x .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _ 

∪-idem : (xs : 𝒦 A) → xs ∪ xs ≡ xs
∪-idem = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ ((xs ∪ xs) ≡ xs)
  alg .fst ∅ = refl
  alg .snd = eq-coh
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) =
    (x ∷ xs) ∪ (x ∷ xs) ≡˘⟨ ∷-distrib x (x ∷ xs) xs ⟩
    x ∷ x ∷ xs ∪ xs ≡⟨ dup x (xs ∪ xs) ⟩
    x ∷ xs ∪ xs ≡⟨ cong (x ∷_) P⟨xs⟩ ⟩
    x ∷ xs ∎

∪-idʳ : (xs : 𝒦 A) → (xs ∪ ∅ ≡ xs)
∪-idʳ = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (xs ∪ ∅ ≡ xs)
  alg .fst ∅ = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = cong (x ∷_) P⟨xs⟩
  alg .snd = eq-coh

∪-com : (xs ys : 𝒦 A) → (xs ∪ ys ≡ ys ∪ xs)
∪-com = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys → xs ∪ ys ≡ ys ∪ xs)
  alg .fst ∅ ys = sym (∪-idʳ ys)
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys = cong (x ∷_) (P⟨xs⟩ ys) ; ∷-distrib x ys xs
  alg .snd = prop-coh λ _ → isPropΠ λ _ → trunc _ _

∪-assoc : (xs ys zs : 𝒦 A) → ((xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
∪-assoc = ⟦ alg ⟧
  where
  alg : Ψ[ xs ⦂ 𝒦 A ] ↦ (∀ ys zs → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs))
  alg .fst ∅ ys zs = refl
  alg .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) ys zs = cong (x ∷_) (P⟨xs⟩ ys zs)
  alg .snd = prop-coh λ _ → isPropΠ λ _ → isPropΠ λ _ → trunc _ _
