{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.List.Relation.Binary.Permutation where

open import Prelude
open import Data.List
open import Data.Fin
open import Data.Fin.Properties
open import Data.List.Membership
open import Cubical.Foundations.Equiv
import Function.Isomorphism as Isomorphism
open import Relation.Binary
open import Cubical.Foundations.Prelude using (J; _∧_)
open import Cubical.Foundations.Transport using (isSet-subst)
open import Cubical.Data.Sigma.Properties
open import Data.Nat.Properties using (znots; snotz)

infixr 0 _↝_
_↝_ : {A : Type a} (xs ys : List A) → Type a
xs ↝ ys = ∀ x → x ∈ xs → x ∈ ys

infix 4 _↭_
_↭_ : {A : Type a} (xs ys : List A) → Type a
xs ↭ ys = ∀ x → (x ∈ xs) ⇔ (x ∈ ys)

reflₚ : ∀ {xs : List A} → xs ↭ xs
reflₚ _ = Isomorphism.refl-⇔

symₚ : {xs ys : List A} → xs ↭ ys → ys ↭ xs
symₚ xs↭ys x = Isomorphism.sym-⇔ (xs↭ys x)

transₚ : {xs ys zs : List A} → xs ↭ ys → ys ↭ zs → xs ↭ zs
transₚ xs↭ys ys↭zs x = Isomorphism.trans-⇔ (xs↭ys x) (ys↭zs x)

consₚ : ∀ x {xs ys : List A} → xs ↭ ys → x ∷ xs ↭ x ∷ ys
consₚ _ xs↭ys _ .fun       (f0   , x≡x )    = f0 , x≡x
consₚ _ xs↭ys _ .fun       (fs n  , x∈xs)    = push (xs↭ys _ .fun (n , x∈xs))
consₚ _ xs↭ys _ .inv       (f0   , x≡x )    = f0 , x≡x
consₚ _ xs↭ys _ .inv       (fs n  , x∈xs)    = push (xs↭ys _ .inv (n , x∈xs))
consₚ _ xs↭ys _ .leftInv   (f0   , x≡x)     = refl
consₚ _ xs↭ys _ .leftInv   (fs n  , x∈xs) i  = push (xs↭ys _ .leftInv (n , x∈xs) i)
consₚ _ xs↭ys _ .rightInv  (f0   , x≡x)     = refl
consₚ _ xs↭ys _ .rightInv  (fs n  , x∈xs) i  = push (xs↭ys _ .rightInv (n , x∈xs) i)

swapₚ-to : ∀ (x₁ x₂ : A) xs → x₁ ∷ x₂ ∷ xs ↝ x₂ ∷ x₁ ∷ xs
swapₚ-to _ _ _ _ (f0 , x≡x₁) = fs f0 , x≡x₁
swapₚ-to _ _ _ _ (fs f0 , x≡x₂) = f0 , x≡x₂
swapₚ-to _ _ _ _ (fs (fs n) , x∈xs) = fs (fs n) , x∈xs

swapₚ-inv : ∀ (x₁ x₂ : A) xs x x∈xs → swapₚ-to x₂ x₁ xs x (swapₚ-to x₁ x₂ xs x x∈xs) ≡ x∈xs
swapₚ-inv _ _ _ _ (f0 , x≡x₁) = refl
swapₚ-inv _ _ _ _ (fs f0 , x≡x₂) = refl
swapₚ-inv _ _ _ _ (fs (fs n) , x∈xs) = refl

swapₚ : ∀ x₁ x₂ (xs : List A) → x₁ ∷ x₂ ∷ xs ↭ x₂ ∷ x₁ ∷ xs
swapₚ x₁ x₂ xs x .fun = swapₚ-to x₁ x₂ xs x
swapₚ x₁ x₂ xs x .inv = swapₚ-to x₂ x₁ xs x
swapₚ x₁ x₂ xs x .leftInv  = swapₚ-inv x₁ x₂ xs x
swapₚ x₁ x₂ xs x .rightInv = swapₚ-inv x₂ x₁ xs x

Fin-length : (xs : List A) → ∃ x × (x ∈ xs) ⇔ Fin (length xs)
Fin-length xs .inv n = xs ! n , n , refl
Fin-length xs .fun (x , n , p) = n
Fin-length xs .leftInv (x , n , p) i .fst = p i
Fin-length xs .leftInv (x , n , p) i .snd .fst = n
Fin-length xs .leftInv (x , n , p) i .snd .snd j = p (i ∧ j)
Fin-length xs .rightInv n = refl

Fin-length-cong : (xs ys : List A) →
                xs ↭ ys →
                Fin (length xs) ⇔ Fin (length ys)
Fin-length-cong xs ys xs↭ys =
  sym-⇔ (Fin-length xs) ⟨ trans-⇔ ⟩ iso-Σ xs↭ys ⟨ trans-⇔ ⟩ Fin-length ys

index-commutes : ∀ (x : A) xs ys →
                 (xs↭ys : xs ↭ ys) (x∈xs : x ∈ xs) →
                 fst (xs↭ys x .fun x∈xs) ≡ Fin-length-cong xs ys xs↭ys .fun (x∈xs .fst)
index-commutes x xs ys xs↭ys (n , p) =
  J (λ y y∈xs → xs↭ys y .fun (n , y∈xs) .fst ≡ xs↭ys (xs ! n) .fun (n , refl) .fst) refl p

index-equality-preserved : ∀ (x : A) xs ys (p q : x ∈ xs) →
                           (xs↭ys : xs ↭ ys) →
                           fst p ≡ fst q →
                           xs↭ys x .fun p .fst ≡ xs↭ys x .fun q .fst
index-equality-preserved x xs ys p q xs↭ys ip≡iq =
  xs↭ys x .fun p .fst ≡⟨ index-commutes x xs ys xs↭ys p ⟩
  Fin-length-cong xs ys xs↭ys .fun (p .fst) ≡⟨ cong (Fin-length-cong xs ys xs↭ys .fun) ip≡iq ⟩
  Fin-length-cong xs ys xs↭ys .fun (q .fst) ≡˘⟨ index-commutes x xs ys xs↭ys q ⟩
  xs↭ys x .fun q .fst ∎
  where open import Path.Reasoning

perm-inj : ∀ (x : A) xs ys n →
         (xs↭ys : x ∷ xs ↭ x ∷ ys) →
         ∀ z
         (z∈ys : x ≡ z)
         (x∈ys : x ≡ z)
         (z∈xs : xs ! n ≡ z)
         (p₁ : xs↭ys z .fun (fs n , z∈xs) ≡ (f0 , z∈ys))
         (p₂ : xs↭ys z .fun (f0 , z∈ys) ≡ (f0 , x∈ys)) →
         ⊥
perm-inj x xs ys n xs↭ys z z∈ys x∈ys z∈xs p₁ p₂ = znots (cong FinToℕ p₆)
  where
  open import Path.Reasoning

  p₃ = fs n , z∈xs ≡˘⟨ xs↭ys z .leftInv (fs n , z∈xs) ⟩
       xs↭ys z .inv (xs↭ys z .fun (fs n , z∈xs)) ≡⟨ cong (xs↭ys z .inv) p₁ ⟩
       xs↭ys z .inv (f0 , z∈ys) ∎

  p₄ = f0 , z∈ys ≡˘⟨ xs↭ys z .leftInv (f0 , z∈ys) ⟩
       xs↭ys z .inv (xs↭ys z .fun (f0 , z∈ys)) ≡⟨ cong (xs↭ys z .inv) p₂ ⟩
       xs↭ys z .inv (f0 , x∈ys) ∎

  p₅ = index-equality-preserved z (x ∷ ys) (x ∷ xs) (f0 , x∈ys) (f0 , z∈ys) (sym-⇔ ∘ xs↭ys) refl

  p₆ = f0 ≡⟨ cong fst p₄ ⟩
       xs↭ys z .inv (f0 , x∈ys) .fst ≡⟨ p₅ ⟩
       xs↭ys z .inv (f0 , z∈ys) .fst ≡˘⟨ cong fst p₃ ⟩
       fs n ∎

tailₚ-to : ∀ x (xs ys : List A) → x ∷ xs ↭ x ∷ ys → ∀ z → z ∈ xs → z ∈ ys
tailₚ-to x xs ys xs↭ys z (n , z∈xs) with xs↭ys z .fun (fs n , z∈xs) | inspect (xs↭ys z .fun) (fs n , z∈xs)
... | fs m , z∈ys | _ = m , z∈ys
... | f0 , z∈ys | 〖 p₁ 〗 with xs↭ys z .fun (f0 , z∈ys) | inspect (xs↭ys z .fun) (f0 , z∈ys)
... | fs o , x∈ys | _ = o , x∈ys
... | f0 , x∈ys | 〖 p₂ 〗 = ⊥-elim (perm-inj x xs ys n xs↭ys z z∈ys x∈ys z∈xs p₁ p₂)

pred-∈-eq : ∀ (x y : A) xs i j →
          (x∈xs₁ : xs ! i ≡ x) →
          (x∈xs₂ : xs ! j ≡ x) →
          Path (x ∈ y ∷ xs) (fs i , x∈xs₁) (fs j , x∈xs₂) →
          (i , x∈xs₁) ≡ (j , x∈xs₂)
pred-∈-eq x y xs i j x∈xs₁ x∈xs₂ =
  J (λ { (fs n , x∈xs₃) _ → (i , x∈xs₁) ≡ (n , x∈xs₃)
       ; (f0     , x∈xs₃) → ⊥-elim ∘ snotz ∘ cong FinToℕ ∘ cong fst })
  refl

open import Path.Reasoning

tailₚ-inv : ∀ x (xs ys : List A) →
            (xs↭ys : x ∷ xs ↭ x ∷ ys) →
            ∀ z (i : z ∈ ys) →
            tailₚ-to x xs ys xs↭ys z (tailₚ-to x ys xs (sym-⇔ ∘ xs↭ys) z i)  ≡ i
tailₚ-inv x xs ys xs↭ys z (n , z∈ys) with xs↭ys z .inv (fs n , z∈ys) | inspect (xs↭ys z .inv) (fs n , z∈ys)
... | fs m , z∈xs  | 〖 p₁ 〗 with xs↭ys z .fun (fs m , z∈xs) | inspect (xs↭ys z .fun) (fs m , z∈xs)
... | fs o , z∈ys₂ | 〖 p₂ 〗 = pred-∈-eq z x ys o n z∈ys₂ z∈ys p₃

  where p₃ = fs o , z∈ys₂ ≡˘⟨ p₂ ⟩
             xs↭ys z .fun (fs m , z∈xs) ≡˘⟨ cong (xs↭ys z .fun) p₁ ⟩
             xs↭ys z .fun (xs↭ys z .inv (fs n , z∈ys)) ≡⟨ xs↭ys z .rightInv (fs n , z∈ys) ⟩
             fs n , z∈ys ∎

... | f0     , z∈ys₂ | 〖 p₂ 〗 with xs↭ys z .fun (f0 , z∈ys₂) | inspect (xs↭ys z .fun) (f0 , z∈ys₂)
... | f0     , x∈ys₃ | 〖 p₃ 〗 = ⊥-elim (perm-inj x xs ys m xs↭ys z z∈ys₂ x∈ys₃ z∈xs p₂ p₃)
... | fs o , x∈ys₃ | 〖 p₃ 〗 = ⊥-elim (snotz (cong (FinToℕ ∘ fst) p₄))

  where p₄ = fs n , z∈ys ≡˘⟨ xs↭ys z .rightInv (fs n , z∈ys) ⟩
             xs↭ys z .fun (xs↭ys z .inv (fs n , z∈ys)) ≡⟨ cong (xs↭ys z .fun) p₁ ⟩
             xs↭ys z .fun (fs m , z∈xs) ≡⟨ p₂ ⟩
             f0 , z∈ys₂ ∎

tailₚ-inv x xs ys xs↭ys z (n , z∈ys) | f0 , z∈xs | 〖 p₁ 〗
  with xs↭ys z .inv (f0 , z∈xs) | inspect (xs↭ys z .inv) (f0 , z∈xs)
... | f0     , z∈ys₂ | 〖 p₂ 〗 = ⊥-elim (perm-inj x ys xs n (sym-⇔ ∘ xs↭ys) z z∈xs z∈ys₂ z∈ys p₁ p₂)
... | fs o , z∈ys₂ | 〖 p₂ 〗 with xs↭ys z .fun (fs o , z∈ys₂) | inspect (xs↭ys z .fun) (fs o , z∈ys₂)
... | fs m , z∈ys₃ | 〖 p₃ 〗 = ⊥-elim (snotz (cong (FinToℕ ∘ fst) p₄))

  where p₄ = fs m , z∈ys₃ ≡˘⟨ p₃ ⟩
             xs↭ys z .fun (fs o , z∈ys₂) ≡˘⟨ cong (xs↭ys z .fun) p₂ ⟩
             xs↭ys z .fun (xs↭ys z .inv (f0 , z∈xs)) ≡⟨ xs↭ys z .rightInv (f0 , z∈xs) ⟩
             f0 , z∈xs ∎

... | f0     , z∈ys₃ | 〖 p₃ 〗 with xs↭ys z .fun (f0 , z∈ys₃) | inspect (xs↭ys z .fun) (f0 , z∈ys₃)
... | f0     , z∈ys₄ | 〖 p₄ 〗 = ⊥-elim (perm-inj x xs ys o xs↭ys z z∈ys₃ z∈ys₄ z∈ys₂ p₃ p₄)
... | fs l , z∈ys₄ | 〖 p₄ 〗 = pred-∈-eq z x ys l n z∈ys₄ z∈ys p₇
  where

  p₅ : Path (z ∈ x ∷ ys) (f0 , z∈xs) (f0 , z∈ys₃)
  p₅ = (f0 , z∈xs) ≡˘⟨ xs↭ys z .rightInv (f0 , z∈xs) ⟩
       xs↭ys z .fun (xs↭ys z .inv (f0 , z∈xs)) ≡⟨ cong (xs↭ys z .fun) p₂ ⟩
       xs↭ys z .fun (fs o , z∈ys₂) ≡⟨ p₃ ⟩
       (f0 , z∈ys₃) ∎

  p₆ = z∈xs ≡˘⟨ isSet-subst {B = λ n → (x ∷ ys) ! n ≡ z} (Discrete→isSet discreteFin) (cong fst p₅) z∈xs ⟩
       subst (λ n → (x ∷ ys) ! n ≡ z) (cong fst p₅) z∈xs
     ≡⟨ PathΣ→ΣPathTransport (f0 , z∈xs) (f0 , z∈ys₃) p₅ .snd ⟩
       z∈ys₃ ∎

  p₇ = fs l , z∈ys₄ ≡˘⟨ p₄ ⟩
       xs↭ys z .fun (f0 , z∈ys₃) ≡˘⟨ cong (xs↭ys z .fun ∘ _,_ f0) p₆ ⟩
       xs↭ys z .fun (f0 , z∈xs) ≡˘⟨ cong (xs↭ys z .fun) p₁ ⟩
       xs↭ys z .fun (xs↭ys z .inv (fs n , z∈ys)) ≡⟨ xs↭ys z .rightInv (fs n , z∈ys) ⟩
       fs n , z∈ys ∎

tailₚ : ∀ x (xs ys : List A) →
        x ∷ xs ↭ x ∷ ys →
        xs ↭ ys
tailₚ x xs ys x∷xs↭x∷ys k .fun = tailₚ-to x xs ys x∷xs↭x∷ys k
tailₚ x xs ys x∷xs↭x∷ys k .inv = tailₚ-to x ys xs (sym-⇔ ∘ x∷xs↭x∷ys) k
tailₚ x xs ys x∷xs↭x∷ys k .rightInv = tailₚ-inv x xs ys x∷xs↭x∷ys k
tailₚ x xs ys x∷xs↭x∷ys k .leftInv  v = cong (λ z → tailₚ-to x ys xs (sym-⇔ ∘ x∷xs↭x∷ys) k (tailₚ-to x xs ys z k v)) (funExt (λ h → sym (sym-sym-iso (x∷xs↭x∷ys h)) ))  ; tailₚ-inv x ys xs (sym-⇔ ∘ x∷xs↭x∷ys) k v
