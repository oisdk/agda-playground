{-# OPTIONS --cubical #-}

module Data.List.Permute where

open import Prelude
open import Data.Nat
open import Data.Nat.Properties using (_≤ᴮ_)

infixr 5 _∹_∷_
data Premuted {a} (A : Type a) : Type a where
 [] : Premuted A
 _∹_∷_ : ℕ → A → Premuted A → Premuted A

mutual
  merge : Premuted A → Premuted A → Premuted A
  merge [] = id
  merge (n ∹ x ∷ xs) = mergeˡ n x (merge xs)

  mergeˡ : ℕ → A → (Premuted A → Premuted A) → Premuted A → Premuted A
  mergeˡ i x xs [] = i ∹ x ∷ xs []
  mergeˡ i x xs (j ∹ y ∷ ys) = merge⁺ i x xs j y ys (i ≤ᴮ j)

  merge⁺ : ℕ → A → (Premuted A → Premuted A) → ℕ → A → Premuted A → Bool → Premuted A
  merge⁺ i x xs j y ys true  = i ∹ x ∷ xs ((j ∸ i) ∹ y ∷ ys)
  merge⁺ i x xs j y ys false = j ∹ y ∷ mergeˡ ((i ∸ j) ∸ 1) x xs ys

merge-idʳ : (xs : Premuted A) → merge xs [] ≡ xs
merge-idʳ [] = refl
merge-idʳ (i ∹ x ∷ xs) = cong (i ∹ x ∷_) (merge-idʳ xs)

open import Algebra

≤≡-trans : ∀ x y z → (x ≤ᴮ y) ≡ true → (y ≤ᴮ z) ≡ true → (x ≤ᴮ z) ≡ true
≤≡-trans zero y z p₁ p₂ = refl
≤≡-trans (suc x) zero z p₁ p₂ = ⊥-elim (subst (bool ⊤ ⊥) p₁ tt)
≤≡-trans (suc x) (suc y) zero p₁ p₂ = ⊥-elim (subst (bool ⊤ ⊥) p₂ tt)
≤≡-trans (suc x) (suc y) (suc z) p₁ p₂ = ≤≡-trans x y z p₁ p₂

<≡-trans : ∀ x y z → (x ≤ᴮ y) ≡ false → (y ≤ᴮ z) ≡ false → (x ≤ᴮ z) ≡ false
<≡-trans zero y z p₁ p₂ = ⊥-elim (subst (bool ⊥ ⊤) p₁ tt)
<≡-trans (suc x) zero z p₁ p₂ = ⊥-elim (subst (bool ⊥ ⊤) p₂ tt)
<≡-trans (suc x) (suc y) zero p₁ p₂ = p₂
<≡-trans (suc x) (suc y) (suc z) p₁ p₂ = <≡-trans x y z p₁ p₂

≤≡-sub : ∀ i j k → (j ≤ᴮ k) ≡ true → (j ∸ i ≤ᴮ k ∸ i) ≡ true
≤≡-sub zero j k p = p
≤≡-sub (suc i) zero k p = refl
≤≡-sub (suc i) (suc j) zero p = ⊥-elim (subst (bool ⊤ ⊥) p tt)
≤≡-sub (suc i) (suc j) (suc k) p = ≤≡-sub i j k p

≥≡-sub : ∀ i j k → (j ≤ᴮ k) ≡ false → (i ≤ᴮ k) ≡ true → (j ∸ i ≤ᴮ k ∸ i) ≡ false
≥≡-sub i zero k p _ = ⊥-elim (subst (bool ⊥ ⊤) p tt)
≥≡-sub zero (suc j) k p _ = p
≥≡-sub (suc i) (suc j) zero p p₂ = ⊥-elim (subst (bool ⊤ ⊥) p₂ tt)
≥≡-sub (suc i) (suc j) (suc k) p p₂ = ≥≡-sub i j k p p₂

<≡-sub : ∀ i j k → (i ≤ᴮ j) ≡ false → (j ≤ᴮ k) ≡ false → (i ∸ k ∸ 1 ≤ᴮ j ∸ k ∸ 1) ≡ false
<≡-sub zero j k p _ = ⊥-elim (subst (bool ⊥ ⊤) p tt)
<≡-sub (suc i) zero k p p₂ = ⊥-elim (subst (bool ⊥ ⊤) p₂ tt)
<≡-sub (suc i) (suc j) zero p p₂ = p
<≡-sub (suc i) (suc j) (suc k) p p₂ = <≡-sub i j k p p₂

>≡-sub : ∀ i j k → (i ≤ᴮ j) ≡ true → (j ≤ᴮ k) ≡ false → (i ≤ᴮ k) ≡ false → (i ∸ k ∸ 1 ≤ᴮ j ∸ k ∸ 1) ≡ true
>≡-sub i zero    k p₁ p₂ p₃ = ⊥-elim (subst (bool ⊥ ⊤) p₂ tt)
>≡-sub zero (suc j) k p₁ p₂ p₃ = ⊥-elim (subst (bool ⊥ ⊤) p₃ tt)
>≡-sub (suc i) (suc j) zero p₁ p₂ p₃ = p₁
>≡-sub (suc i) (suc j) (suc k) p₁ p₂ p₃ = >≡-sub i j k p₁ p₂ p₃

zero-sub : ∀ n → zero ∸ n ≡ zero
zero-sub zero = refl
zero-sub (suc n) = refl

≤-sub-id : ∀ i j k → (i ≤ᴮ j) ≡ true → k ∸ i ∸ (j ∸ i) ≡ k ∸ j
≤-sub-id zero j k p = refl
≤-sub-id (suc i) zero k p = ⊥-elim (subst (bool ⊤ ⊥) p tt)
≤-sub-id (suc i) (suc j) zero p = zero-sub (j ∸ i)
≤-sub-id (suc i) (suc j) (suc k) p = ≤-sub-id i j k p

lemma₁ : ∀ i j k → (j ≤ᴮ k) ≡ false → i ∸ k ∸ 1 ∸ (j ∸ k ∸ 1) ∸ 1 ≡ i ∸ j ∸ 1
lemma₁ zero j k _ = cong (λ zk → zk ∸ 1 ∸ (j ∸ k ∸ 1) ∸ 1) (zero-sub k) ; cong (_∸ 1) (zero-sub (j ∸ k ∸ 1)) ; sym (cong (_∸ 1) (zero-sub j))
lemma₁ (suc i) zero k p₂ = ⊥-elim (subst (bool ⊥ ⊤) p₂ tt)
lemma₁ (suc i) (suc j) zero p₂ = refl
lemma₁ (suc i) (suc j) (suc k) p₂ = lemma₁ i j k p₂

lemma₂ : ∀ i j k → (i ≤ᴮ j) ≡ true → (j ≤ᴮ k) ≡ false → (i ≤ᴮ k) ≡ false → j ∸ i ≡ j ∸ k ∸ 1 ∸ (i ∸ k ∸ 1)
lemma₂ i zero    k p₁ p₂ p₃ = ⊥-elim (subst (bool ⊥ ⊤) p₂ tt)
lemma₂ zero (suc j) k p₁ p₂ p₃ = ⊥-elim (subst (bool ⊥ ⊤) p₃ tt)
lemma₂ (suc i) (suc j) zero p₁ p₂ p₃ = refl
lemma₂ (suc i) (suc j) (suc k) p₁ p₂ p₃ = lemma₂ i j k p₁ p₂ p₃

{-# TERMINATING #-}
merge-assoc : Associative (merge {A = A})
merge-assoc [] ys zs = refl
merge-assoc (i ∹ x ∷ xs) [] zs = cong (flip merge zs) (merge-idʳ (i ∹ x ∷ xs))
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) [] = merge-idʳ (merge (i ∹ x ∷ xs) (j ∹ y ∷ ys)) ; sym (cong (merge (i ∹ x ∷ xs)) (merge-idʳ (j ∹ y ∷ ys)))
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) with i ≤ᴮ j | inspect (i ≤ᴮ_) j | j ≤ᴮ k | inspect (j ≤ᴮ_) k
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true  | 〖 ij 〗 | true  | 〖 jk 〗 = cong (merge⁺ i x (merge (merge xs (j ∸ i ∹ y ∷ ys))) k z zs) (≤≡-trans i j k ij jk) ;
                                                                                          cong (i ∹ x ∷_) (merge-assoc xs (j ∸ i ∹ y ∷ ys) (k ∸ i ∹ z ∷ zs) ;
                                                                                          cong (merge xs) (cong (merge⁺ (j ∸ i) y (merge ys) (k ∸ i) z zs) (≤≡-sub i j k jk) ; cong (λ kij → j ∸ i ∹ y ∷ merge ys (kij ∹ z ∷ zs)) (≤-sub-id i j k ij))) ;
                                                                                          cong (merge⁺ i x (merge xs) j y (merge ys (k ∸ j ∹ z ∷ zs))) (sym ij)
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | false | 〖 ij 〗 | false | 〖 jk 〗 = cong (merge⁺ j y (merge (mergeˡ (i ∸ j ∸ 1) x (merge xs) ys)) k z zs ) jk ;
                                                                                          cong (k ∹ z ∷_) (cong (λ s → mergeˡ (j ∸ k ∸ 1) y (merge (mergeˡ s x (merge xs) ys)) zs) (sym (lemma₁ i j k jk)) ;
                                                                                          cong (λ s → merge (merge⁺ (i ∸ k ∸ 1) x (merge xs) (j ∸ k ∸ 1) y ys s) zs) (sym (<≡-sub i j k ij jk)) ;
                                                                                          merge-assoc (i ∸ k ∸ 1 ∹ x ∷ xs) (j ∸ k ∸ 1 ∹ y ∷ ys) zs) ;
                                                                                          cong (merge⁺ i x (merge xs) k z (mergeˡ (j ∸ k ∸ 1) y (merge ys) zs)) (sym (<≡-trans i j k ij jk))
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | false | 〖 ij 〗 | true  | 〖 jk 〗 = cong (merge⁺ j y (merge (mergeˡ (i ∸ j ∸ 1) x (merge xs) ys)) k z zs) jk ;
                                                                                          cong (j ∹ y ∷_) (merge-assoc (i ∸ j ∸ 1 ∹ x ∷ xs) ys (k ∸ j ∹ z ∷ zs)) ;
                                                                                          cong (merge⁺ i x (merge xs) j y (merge ys (k ∸ j ∹ z ∷ zs))) (sym ij)
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true  | ij | false | jk with i ≤ᴮ k | inspect (i ≤ᴮ_) k
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true | 〖 ij 〗 | false | 〖 jk 〗 | false | 〖 ik 〗 = cong (k ∹ z ∷_) ((cong (λ s → mergeˡ (i ∸ k ∸ 1) x (merge (merge xs (s ∹ y ∷ ys))) zs) (lemma₂ i j k ij jk ik) ;
                                                                                                           cong (λ c → merge (merge⁺ (i ∸ k ∸ 1) x (merge xs) (j ∸ k ∸ 1) y ys c) zs) (sym (>≡-sub i j k ij jk ik ))) ;
                                                                                                           merge-assoc (i ∸ k ∸ 1 ∹ x ∷ xs) (j ∸ k ∸ 1 ∹ y ∷ ys) zs)
merge-assoc (i ∹ x ∷ xs) (j ∹ y ∷ ys) (k ∹ z ∷ zs) | true | 〖 ij 〗 | false | 〖 jk 〗 | true  | 〖 ik 〗 = cong (i ∹ x ∷_) (merge-assoc xs (j ∸ i ∹ y ∷ ys) (k ∸ i ∹ z ∷ zs) ;
                                                                                                             cong (merge xs) (cong (merge⁺ (j ∸ i) y (merge ys) (k ∸ i) z zs) (≥≡-sub i j k jk ik) ;
                                                                                                             cong (λ s → k ∸ i ∹ z ∷ mergeˡ s y (merge ys) zs) (cong (_∸ 1) (≤-sub-id i k j ik)) ))
