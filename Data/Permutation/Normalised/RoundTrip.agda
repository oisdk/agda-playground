{-# OPTIONS --safe #-}

module Data.Permutation.Normalised.RoundTrip where

open import Prelude hiding (_↔_)
open import Data.List hiding ([]; _∷_)
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Permutation.Swap _≟_
open import Data.Permutation.NonNorm _≟_
open import Data.Nat using (_+_)
open import Data.Permutation.Normalised.Definition
open import Data.List.Properties
open import Data.Permutation.Normalised.Unnorm
open import Data.Permutation.Normalised.Norm
open import Data.Nat.Compare
open import Path.Reasoning
open import Data.Maybe

unf-coalg : ℕ → ℕ → (ℕ → Diffs) → ℕ → Diffs
unf-coalg x y k n = k (suc n + x) ∘⟨ n + x , y ⟩ 

un-diff : Diffs → ℕ → Diffs
un-diff = foldr (uncurry unf-coalg) (const ⟨⟩)

compare-diff-+ : ∀ x y → compare x (suc x + y) ≡ less y
compare-diff-+ zero y = refl
compare-diff-+ (suc x) y = compare-diff-+ x y

norm-lemma₁ : ∀ xs x y → xs ⊙+ suc x ⊙⟨ x , y ⟩ ≡ xs ∘⟨ x , y ⟩
norm-lemma₁ ⟨⟩ x y = refl
norm-lemma₁ (xs ∘⟨ s , t ⟩) x y with compare x (suc x + s) | comparing x (suc x + s)
... | less    k | sx+k≡sx+s = cong (λ e → xs ∘⟨ e , t ⟩ ∘⟨ x , y ⟩) (+-inj (suc x) sx+k≡sx+s)
... | equal     | x≡sx+s = ⊥-elim (x≢sx+y x s x≡sx+s)
... | greater k | p = ⊥-elim (x≢sx+y x (suc s + k) (sym p ; cong suc (cong suc (+-assoc x s k) ; sym (+-suc x (s + k)))))

norm-lemma : ∀ xs n → foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs n) ≡ xs ⊙+ n
norm-lemma ⟨⟩ n = refl
norm-lemma (xs ∘⟨ x , y ⟩) n =
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff (xs ∘⟨ x , y ⟩) n) ≡⟨⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs (suc n + x) ∘⟨ n + x , y ⟩) ≡⟨⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs (suc n + x)) ⊙⟨ n + x , y ⟩ ≡⟨ cong (_⊙⟨ n + x , y ⟩) (norm-lemma xs (suc n + x)) ⟩
  xs ⊙+ suc n + x ⊙⟨ n + x , y ⟩ ≡⟨ norm-lemma₁ xs (n + x) y ⟩
  xs ∘⟨ n + x , y ⟩ ∎

norm-inv : ∀ xs → [ [ xs ]↑ ]↓ ≡ xs
norm-inv xs =
  [ [ xs ]↑ ]↓ ≡⟨⟩
  [ foldr (uncurry unflatten-alg) (const ⟨⟩) xs 0 ]↓ ≡⟨⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (catMaybes (uncurry swap-diff) (foldr (uncurry unflatten-alg) (const ⟨⟩) xs 0))
    ≡⟨ cong′ {A = ℕ → Swaps} (λ k → foldr (flip _⊙⟨_⟩) ⟨⟩ (k 0)) (foldr-fusion (λ xs n → catMaybes (uncurry swap-diff) (xs n)) (const ⟨⟩) (λ { (x , y) k → funExt λ n → cong (maybe _ _) (cong (mapMaybe (map₁ (bool′ (n + x) _))) (compare-diff-+ (n + x) y)) }) xs) ⟩
  foldr (flip _⊙⟨_⟩) ⟨⟩ (un-diff xs 0)
    ≡⟨  norm-lemma xs 0 ⟩
  xs ⊙+ 0
    ≡⟨ shift-0 xs ⟩
  xs ∎
