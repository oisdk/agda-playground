{-# OPTIONS --cubical --safe #-}

module Control.Monad.Levels.Zipping where

open import Prelude
open import Control.Monad.Levels.Definition
open import Control.Monad.Levels.Eliminators
open import Data.Bag

open import Cubical.Foundations.HLevels using (isOfHLevelΠ)

zip₂-alg : Levels-ϕ[ A ](⟅ A ⟆ → (Levels A → Levels A) → Levels A)
[ zip₂-alg ]-set = isOfHLevelΠ 2 λ _ → isOfHLevelΠ 2 λ _ → trunc
[ zip₂-alg ] y ∷ ys ⟨ _ ⟩ x xs = (x ∪ y) ∷ xs ys
[ zip₂-alg ][] x xs = x ∷ xs []
[ zip₂-alg ]-trail i x xs = ∪-idʳ x i ∷ xs []

zip₂-alg-id : Levels-ψ[ xs ⦂ A ]≡ ((zip₂-alg ↓ xs) [] id ⊜ xs)
⟦ zip₂-alg-id ⟧≡ x ∷ xs ⟨ Pxs ⟩ = refl
⟦ zip₂-alg-id ⟧≡[] = trail

zip-alg : Levels-ϕ[ A ] (Levels A → Levels A)
[ zip-alg ]-set = isOfHLevelΠ 2 λ _ → trunc
[ zip-alg ] x ∷ _ ⟨ k ⟩ ys = (zip₂-alg ↓ ys) x k
[ zip-alg ][] ys = ys
[ zip-alg ]-trail = funExt (zip₂-alg-id ⇓≡_)

zip : Levels A → Levels A → Levels A
zip xs = zip-alg ↓ xs

zip-idʳ : Levels-ψ[ xs ⦂ A ]≡ zip xs [] ⊜ xs
⟦ zip-idʳ ⟧≡ x ∷ xs ⟨ Pxs ⟩ = cong (x ∷_) Pxs
⟦ zip-idʳ ⟧≡[] = refl


-- zip-comm : (ys : Levels A) → Levels-ψ[ xs ⦂ A ]≡ (zip xs ys ⊜ zip ys xs)
-- ⟦ zip-comm ys ⟧≡ x ∷ xs ⟨ Pxs ⟩ = {!!}
-- ⟦ zip-comm ys ⟧≡[] = sym (zip-idʳ ⇓≡ ys)
