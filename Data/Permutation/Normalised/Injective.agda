{-# OPTIONS --safe #-}

module Data.Permutation.Normalised.Injective where

open import Prelude hiding (_↔_)
open import Data.List hiding ([]; _∷_)
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Permutation.Swap _≟_
open import Data.Permutation.NonNorm _≟_
open import Data.Nat using (_+_)
open import Data.Permutation.Normalised.Definition
open import Data.List.Properties
open import Data.Permutation.Normalised.Unnorm
open import Data.Nat.Compare

step-lemma : ∀ x y xs ys → (∀ n → xs ∘⟨ x , y ⟩ ⊙ n ≡ ys ∘⟨ x , y ⟩ ⊙ n) → ∀ n → xs ⊙ n ≡ ys ⊙ n
step-lemma x y xs ys p n with y ≟ n 
... | no y≢n =
  let h =
        sym (cong (λ e → xs ⊙+ suc x ⊙ e) (swap-neq x (suc x + y) (suc x + n) (x≢sx+y x n) (y≢n ∘ +-inj (suc x)))
        ; ⊙+⊙ (suc x) _ xs)
        ; sym (⊙-alg-com x y xs (suc x + n) ; cong′ {A = ℕ} (λ e → xs ⊙+ suc x ⊙ e) (⊙-· x y (suc (x + n))))
        ; p (suc x + n)
        ; ⊙-alg-com x y ys (suc x + n) ; cong′ {A = ℕ} (λ e → ys ⊙+ suc x ⊙ e) (⊙-· x y (suc (x + n)))
        ; cong (λ e → ys ⊙+ suc x ⊙ e) (swap-neq x (suc x + y) (suc x + n) (x≢sx+y x n) (y≢n ∘ +-inj (suc x)))
        ; ⊙+⊙ (suc x) _ ys
  in +-inj (suc x) h
... | yes y≡n =
  let h = sym (⊙-alg-com x y xs x ; cong (λ e → xs ⊙+ suc x ⊙ e) (⊙-· x y x ; swap-lhs x _) ; ⊙+⊙ (suc x) y xs)
        ; p x
        ; ⊙-alg-com x y ys x ; cong (λ e → ys ⊙+ suc x ⊙ e) (⊙-· x y x ; swap-lhs x _) ; ⊙+⊙ (suc x) y ys
  in  cong (xs ⊙_) (sym y≡n) ; +-inj (suc x) h ; cong (ys ⊙_) y≡n

⊙-inj : ∀ xs n m → xs ⊙ n ≡ xs ⊙ m → n ≡ m
⊙-inj xs n m p = perm-inj [ xs ]↑ n m (sym (⊙↑-hom xs n) ; p ; ⊙↑-hom xs m)

inj-⊙-lemma : ∀ x xₜ yₜ xs ys
            → (∀ n → xs ∘⟨ x , xₜ ⟩ ⊙ n ≡ ys ∘⟨ x , yₜ ⟩ ⊙ n)
            → xₜ ≢ yₜ
            → xs ⊙ xₜ ≡ ys ⊙ yₜ
            → ∀ n
            → xs ⊙ n ≡ ys ⊙ n
inj-⊙-lemma x xₜ yₜ xs ys p xₜ≢yₜ xye n with n ≟ xₜ | n ≟ yₜ
... | yes n≡xₜ | yes n≡yₜ = ⊥-elim (xₜ≢yₜ (sym n≡xₜ ; n≡yₜ))
... | no  n≢xₜ | yes n≡yₜ =
  ⊥-elim (x≢sx+y x (xs ⊙ n) (sym (sym (⊙-lhs x xₜ xs n (n≢xₜ ∘ sym)) ; p (suc x + n) ; cong (λ e → ys ∘⟨ x , yₜ ⟩ ⊙ suc x + e) n≡yₜ  ; ⊙-rhs x yₜ ys)))
... | yes n≡xₜ | no  n≢yₜ =
  ⊥-elim (x≢sx+y x (ys ⊙ n)
    ( sym (⊙-rhs x xₜ xs)
    ; cong (λ e → xs ∘⟨ x , xₜ ⟩ ⊙ suc x + e) (sym n≡xₜ)
    ; p (suc x + n)
    ; ⊙-lhs x yₜ ys n (n≢yₜ ∘ sym)
    ))
... | no  n≢xₜ | no  n≢yₜ =
  +-inj (suc x) (sym (⊙-lhs x xₜ xs n (n≢xₜ ∘ sym)) ; p (suc x + n) ; ⊙-lhs x yₜ ys n (n≢yₜ ∘ sym))

inj-⊙ : ∀ xs ys → (∀ n → xs ⊙ n ≡ ys ⊙ n) → xs ≡ ys
inj-⊙ ⟨⟩ ⟨⟩ _ = refl
inj-⊙ ⟨⟩ (ys ∘⟨ x , y ⟩) p = ⊥-elim (⊙-lhs-neq x y ys (sym (p x)))
inj-⊙ (xs ∘⟨ x , y ⟩) ⟨⟩ p = ⊥-elim (⊙-lhs-neq x y xs (p x))
inj-⊙ (xs ∘⟨ xₛ , xₜ ⟩) (ys ∘⟨ yₛ , yₜ ⟩) p with xₛ ≟ yₛ | xₜ ≟ yₜ

... | yes xₛ≡yₛ | yes xₜ≡yₜ = cong₂ _∘⟨_⟩ (inj-⊙ xs ys  λ n → step-lemma xₛ xₜ xs ys (_; cong₂ (λ e₁ e₂ → ys ∘⟨ e₁ , e₂ ⟩ ⊙ _) (sym xₛ≡yₛ) (sym xₜ≡yₜ) ∘ p) n ) (cong₂ _,_ xₛ≡yₛ xₜ≡yₜ)
... | yes xₛ≡yₛ | no xₜ≢yₜ =
  let h = +-inj (suc xₛ) $ sym (⊙-alg-com xₛ xₜ xs xₛ ; cong (λ e → xs ⊙+ suc xₛ ⊙ e) (⊙-· xₛ xₜ xₛ ; swap-lhs xₛ _) ; ⊙+⊙ (suc xₛ) xₜ xs)
        ; p xₛ
        ; cong (ys ∘⟨ yₛ , yₜ ⟩ ⊙_) xₛ≡yₛ
        ; ⊙-alg-com yₛ yₜ ys yₛ ; cong (λ e → ys ⊙+ suc yₛ ⊙ e) (⊙-· yₛ yₜ yₛ ; swap-lhs yₛ _) ; ⊙+⊙ (suc yₛ) yₜ ys
        ; cong suc (cong (_+ (ys ⊙ yₜ)) (sym xₛ≡yₛ)) 
      h′ = inj-⊙ xs ys (inj-⊙-lemma xₛ xₜ yₜ xs ys ( λ n → p n ; cong (λ e → ys ∘⟨ e , yₜ ⟩ ⊙ n) (sym xₛ≡yₛ) ) xₜ≢yₜ h )
          
      h″ = ⊙-inj xs xₜ yₜ (h ; cong (_⊙ yₜ) (sym h′))
  in ⊥-elim (xₜ≢yₜ h″)
... | no  xₛ≢yₛ | _ with compare xₛ yₛ | comparing xₛ yₛ
... | equal | xₛ≡yₛ = ⊥-elim (xₛ≢yₛ xₛ≡yₛ)
... | less    k | xₛ<yₛ =
  ⊥-elim (⊙-lhs-neq xₛ xₜ xs (p xₛ ; cong (λ e → ys ∘⟨ e , yₜ ⟩ ⊙ xₛ) (sym xₛ<yₛ) ; ⊙-lt (ys ∘⟨ k , yₜ ⟩) xₛ))
... | greater k | yₛ<xₛ =
  ⊥-elim (⊙-lhs-neq yₛ yₜ ys (sym (p yₛ) ; cong (λ e → xs ∘⟨ e , xₜ ⟩ ⊙ yₛ) (sym yₛ<xₛ) ; ⊙-lt (xs ∘⟨ k , xₜ ⟩) yₛ))
