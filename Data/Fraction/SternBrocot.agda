{-# OPTIONS --cubical --safe #-}

module Data.Fraction.SternBrocot where

open import Prelude
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Bits renaming (Bits to ℚ⁺; [] to 1ℚ; 0∷_ to lℚ; 1∷_ to rℚ)
open import Data.Bits.Equatable

⟦_⇓⟧ : ℚ⁺ → (ℕ × ℕ)
⟦ 1ℚ ⇓⟧ = 1 , 1
⟦ lℚ x ⇓⟧ = let p , q = ⟦ x ⇓⟧ in p , p ℕ.+ q
⟦ rℚ x ⇓⟧ = let p , q = ⟦ x ⇓⟧ in p ℕ.+ q , q

module TerminationProofs where
  Tᴮ⇒≡ : {n m : ℕ} → n ≡ m → T (n ℕ.≡ᴮ m)
  Tᴮ⇒≡ {n} {m} n≡m = subst (λ n′ → T (n ℕ.≡ᴮ n′)) n≡m (ℕ.complete-== n)

  lift-suc-≡ : ∀ {n m} s → m ≡ n → T (suc n ℕ.≡ᴮ s) → T (suc m ℕ.≡ᴮ s)
  lift-suc-≡ {n} {m} s  m≡n p = Tᴮ⇒≡ (cong suc m≡n ; ℕ.sound-== (suc n) s p)

  lemma₁ : ∀ a m → a ℕ.+ m ℕ.+ zero ≡ m ℕ.+ a
  lemma₁ a m = ℕ.+-idʳ (a ℕ.+ m) ; ℕ.+-comm a m

  lemma₂ : ∀ n a m → n ℕ.+ m ℕ.+ suc a ≡ n ℕ.+ suc m ℕ.+ a
  lemma₂ n a m = ℕ.+-assoc n m (suc a) ; cong (n ℕ.+_) (ℕ.+-suc m a) ; sym (ℕ.+-assoc n (suc m) a)

  lemma₃ : ∀ n a → n ℕ.+ a ℕ.+ zero ≡ n ℕ.+ zero ℕ.+ a
  lemma₃ n a = ℕ.+-idʳ (n ℕ.+ a) ; cong (ℕ._+ a) (sym (ℕ.+-idʳ n))

_+1/_+1 : ℕ → ℕ → ℚ⁺
n +1/ m +1 = go zero n m (suc n ℕ.+ m) (Tᴮ⇒≡ (ℕ.+-idʳ (n ℕ.+ m)))
  where
  open TerminationProofs

  go : (a n m : ℕ) → ∀ s → T (suc (n ℕ.+ m ℕ.+ a) ℕ.≡ᴮ s) → ℚ⁺
  go a zero    (suc m) (suc s) p = lℚ (go zero a m s (lift-suc-≡ s (lemma₁ a m) p))
  go a (suc n) (suc m) (suc s) p = go (suc a)  n m s (lift-suc-≡ s (lemma₂ n a m) p)
  go a (suc n) zero    (suc s) p = rℚ (go zero n a s (lift-suc-≡ s (lemma₃ n a) p))
  go a zero    zero    (suc s) p = 1ℚ

e : ℕ × ℕ
e = ⟦ 1 +1/ 9 +1 ⇓⟧

_/_ : ℕ → ℕ → ℚ⁺
suc n / suc m = n +1/ m +1
_ / _ = zero +1/ zero +1

_ : ⟦ 5 / 10 ⇓⟧ ≡ (1 , 2)
_ = refl

_ : ⟦ 51 / 10 ⇓⟧ ≡ (51 , 10)
_ = refl

_ : ⟦ 60 / 100 ⇓⟧ ≡ (3 , 5)
_ = refl
