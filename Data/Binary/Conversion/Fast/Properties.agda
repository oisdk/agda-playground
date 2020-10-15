{-# OPTIONS --cubical --safe #-}

module Data.Binary.Conversion.Fast.Properties where

open import Prelude
open import Data.Binary.Conversion
open import Data.Binary.Definition
open import Data.Binary.Increment
import Data.Binary.Conversion.Fast as F
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Maybe.Sugar
open import Data.Maybe

tail𝔹 : 𝔹 → 𝔹
tail𝔹 0ᵇ = 0ᵇ
tail𝔹 (1ᵇ xs) = xs
tail𝔹 (2ᵇ xs) = xs

tail𝔹-inc : ∀ xs → inc (tail𝔹 (inc xs)) ≡ tail𝔹 (inc (inc (inc xs)))
tail𝔹-inc 0ᵇ = refl
tail𝔹-inc (1ᵇ xs) = refl
tail𝔹-inc (2ᵇ xs) = refl

tail-homo : ∀ n → tail𝔹 (inc ⟦ n ⇑⟧) ≡ ⟦ n ÷ 2 ⇑⟧
tail-homo n = go n ; cong ⟦_⇑⟧ (sym (div-helper-lemma 0 1 n 1))
  where
  go : ∀ n → tail𝔹 (inc ⟦ n ⇑⟧) ≡ ⟦ div-helper′ 1 n 1 ⇑⟧
  go zero = refl
  go (suc zero) = refl
  go (suc (suc n)) = sym (tail𝔹-inc ⟦ n ⇑⟧) ; cong inc (go n)

head𝔹 : 𝔹 → Maybe Bool
head𝔹 0ᵇ = nothing
head𝔹 (1ᵇ xs) = just true
head𝔹 (2ᵇ xs) = just false

head𝔹-inc : ∀ xs → head𝔹 (inc (inc (inc xs))) ≡ head𝔹 (inc xs)
head𝔹-inc 0ᵇ = refl
head𝔹-inc (1ᵇ xs) = refl
head𝔹-inc (2ᵇ xs) = refl

head𝔹-homo : ∀ n → head𝔹 (inc ⟦ n ⇑⟧) ≡ just (rem n 2 ≡ᴮ 0)
head𝔹-homo zero    = refl
head𝔹-homo (suc zero) = refl
head𝔹-homo (suc (suc n)) = head𝔹-inc ⟦ n ⇑⟧ ; head𝔹-homo n

open import Data.Bool.Properties
open import Data.Maybe.Properties

head-tail-cong : ∀ xs ys → head𝔹 xs ≡ head𝔹 ys → tail𝔹 xs ≡ tail𝔹 ys → xs ≡ ys
head-tail-cong 0ᵇ 0ᵇ h≡ t≡ = refl
head-tail-cong 0ᵇ (1ᵇ ys) h≡ t≡ = ⊥-elim (nothing≢just h≡)
head-tail-cong 0ᵇ (2ᵇ ys) h≡ t≡ = ⊥-elim (nothing≢just h≡)
head-tail-cong (1ᵇ xs) 0ᵇ h≡ t≡ = ⊥-elim (just≢nothing h≡)
head-tail-cong (1ᵇ xs) (1ᵇ ys) h≡ t≡ = cong 1ᵇ_ t≡
head-tail-cong (1ᵇ xs) (2ᵇ ys) h≡ t≡ = ⊥-elim (subst (bool ⊥ ⊤) (just-inj h≡) tt)
head-tail-cong (2ᵇ xs) 0ᵇ h≡ t≡ = ⊥-elim (just≢nothing h≡)
head-tail-cong (2ᵇ xs) (1ᵇ ys) h≡ t≡ = ⊥-elim (subst (bool ⊤ ⊥) (just-inj h≡) tt)
head-tail-cong (2ᵇ xs) (2ᵇ ys) h≡ t≡ = cong 2ᵇ_ t≡

≤-pred : ∀ n m → suc n ≤ m → n ≤ m
≤-pred zero m p = tt
≤-pred (suc n) zero p = p
≤-pred (suc zero) (suc n) p = tt
≤-pred (suc (suc n₁)) (suc n) p = ≤-pred (suc n₁) n p

≤-pred-pred : ∀ n m → suc n ≤ suc m → n ≤ m
≤-pred-pred zero m p = tt
≤-pred-pred (suc n) m p = p

≤-suc : ∀ n m → n ≤ m → suc n ≤ suc m
≤-suc zero m p = tt
≤-suc (suc n) m p = p

div2≤ : ∀ n m → n ≤ m → n ÷ 2 ≤ m
div2≤ n m n≤m = subst (_≤ m) (sym (div-helper-lemma 0 1 n 1)) (go n m n≤m)
  where
  go : ∀ n m → n ≤ m → div-helper′ 1 n 1 ≤ m
  go zero m n≤m = tt
  go (suc zero) m n≤m = tt
  go (suc (suc n)) (suc m) n≤m = ≤-suc (div-helper′ 1 n 1) m (go n m (≤-pred n m n≤m))

fast-correct-helper : ∀ n w → n ≤ w → F.toBin-helper n w ≡ ⟦ n ⇑⟧
fast-correct-helper zero    w       p = refl
fast-correct-helper (suc n) (suc w) p =
    $!-≡ _ (F.toBin-helper (n ÷ 2) w) ;
    head-tail-cong _ (inc ⟦ n ⇑⟧)
      (lemma₁ (rem n 2 ≡ᴮ 0) (F.toBin-helper (n ÷ 2) w) ; sym (head𝔹-homo n))
      (lemma₂ (rem n 2 ≡ᴮ 0) (F.toBin-helper (n ÷ 2) w) ; fast-correct-helper (n ÷ 2) w (div2≤ n w (≤-pred-pred n w p)) ; sym (tail-homo n))
  where
  lemma₁ : ∀ x xs → head𝔹 (if x then 1ᵇ xs else 2ᵇ xs) ≡ just x
  lemma₁ false xs = refl
  lemma₁ true xs = refl

  lemma₂ : ∀ x xs → tail𝔹 (if x then 1ᵇ xs else 2ᵇ xs) ≡ xs
  lemma₂ false xs = refl
  lemma₂ true xs = refl

n≤n : ∀ n → n ≤ n
n≤n zero    = tt
n≤n (suc zero) = tt
n≤n (suc (suc n)) = n≤n (suc n)

fast-correct : ∀ n → F.⟦ n ⇑⟧ ≡ ⟦ n ⇑⟧
fast-correct n = fast-correct-helper n n (n≤n n)
