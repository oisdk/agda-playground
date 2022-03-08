\begin{code}
module Data.Set.Bind where

open import Data.Set.Definition
open import Data.Set.Eliminators
open import Data.Set.Union
open import Prelude
open import Path.Reasoning

bind : (A → 𝒦 B) → 𝒦 A → 𝒦 B
bind k = ⟦ alg k ⟧
  where
  alg : (k : A → 𝒦 B) → ψ A (𝒦 B)
  alg k .fst ∅ = ∅
  alg k .fst (x ∷ xs ⟨ P⟨xs⟩ ⟩) = k x ∪ P⟨xs⟩
  alg k .snd .c-trunc _ = trunc
  alg k .snd .c-com x y _ xs =
    k x ∪ k y   ∪ xs ≡˘⟨ ∪-assoc (k x) (k y) xs ⟩
    (k x ∪ k y) ∪ xs ≡⟨ cong (_∪ xs) (∪-com (k x) (k y)) ⟩
    (k y ∪ k x) ∪ xs ≡⟨ ∪-assoc (k y) (k x) xs ⟩
    k y ∪ k x ∪ xs ∎
  alg k .snd .c-dup x _ xs =
    k x ∪ k x ∪ xs ≡˘⟨ ∪-assoc (k x) (k x) xs ⟩
    (k x ∪ k x) ∪ xs ≡⟨ cong (_∪ xs) (∪-idem (k x)) ⟩
    k x ∪ xs ∎
\end{code}
