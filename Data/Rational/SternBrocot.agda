{-# OPTIONS --cubical --safe #-}

module Data.Rational.SternBrocot where

open import Prelude
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Bits renaming (Bits to ℚ⁺; [] to 1ℚ; 0∷_ to lℚ; 1∷_ to rℚ)
open import Data.Bits.Equatable

-- ⟦_⇓⟧ : ℚ⁺ → (ℕ × ℕ)
-- ⟦ 1ℚ ⇓⟧ = 1 , 1
-- ⟦ lℚ x ⇓⟧ = let p , q = ⟦ x ⇓⟧ in p , p ℕ.+ q
-- ⟦ rℚ x ⇓⟧ = let p , q = ⟦ x ⇓⟧ in p ℕ.+ q , q

-- module TerminationProofs where
--   Tᴮ⇒≡ : {n m : ℕ} → n ≡ m → T (n ℕ.≡ᴮ m)
--   Tᴮ⇒≡ {n} {m} n≡m = subst (λ n′ → T (n ℕ.≡ᴮ n′)) n≡m (ℕ.complete-== n)

--   lift-suc-≡ : ∀ {n m} s → m ≡ n → T (n ℕ.≡ᴮ s) → T (m ℕ.≡ᴮ s)
--   lift-suc-≡ {n} {m} s  m≡n p = Tᴮ⇒≡ (m≡n ; ℕ.sound-== (n) s p)

--   lemma₁ : ∀ a m → a ℕ.+ m ℕ.+ zero ≡ m ℕ.+ a
--   lemma₁ a m = ℕ.+-idʳ (a ℕ.+ m) ; ℕ.+-comm a m

--   lemma₂ : ∀ n a m → n ℕ.+ m ℕ.+ suc a ≡ n ℕ.+ suc m ℕ.+ a
--   lemma₂ n a m = ℕ.+-assoc n m (suc a) ; cong (n ℕ.+_) (ℕ.+-suc m a) ; sym (ℕ.+-assoc n (suc m) a)

--   lemma₃ : ∀ n a → n ℕ.+ a ℕ.+ zero ≡ n ℕ.+ zero ℕ.+ a
--   lemma₃ n a = ℕ.+-idʳ (n ℕ.+ a) ; cong (ℕ._+ a) (sym (ℕ.+-idʳ n))

-- _+1/_+1 : ℕ → ℕ → ℚ⁺
-- n +1/ m +1 = go zero n m (n ℕ.+ m)
--   where
--   go : (a n m s : ℕ) → ℚ⁺
--   go a zero    (suc m) (suc s) = lℚ (go zero a m s)
--   go a (suc n) (suc m) (suc s) = go (suc a) n m s
--   go a (suc n) zero    (suc s) = rℚ (go zero n a s)
--   go _ _       _       _       = 1ℚ

euclidian : ℕ → ℕ → ℕ → ℚ⁺
euclidian n m zero    = 1ℚ
euclidian n m (suc s) =
  if n ℕ.≡ᴮ m
  then 1ℚ
  else if n ℕ.<ᴮ m
  then lℚ (euclidian n (m ℕ.∸ (1 ℕ.+ n)) s)
  else rℚ (euclidian (n ℕ.∸ (1 ℕ.+ m)) m s)

normalise-suc : ℕ → ℕ → ℚ⁺
normalise-suc n m = euclidian n m (n ℕ.+ m)

ℚ : Type
ℚ = ℚ⁺

import Data.Rational.Unnormalised as F
open import Data.Rational.Unnormalised using (_/suc_; _/_)
import Data.Integer as ℤ
open import Data.Integer using (ℤ; ⁺; ⁻suc; ⁻)
open import Data.Bits.Fold

zer : (ℕ × ℕ) → (ℕ × ℕ)
zer (p , q) = p , suc p ℕ.+ q

one : (ℕ × ℕ) → (ℕ × ℕ)
one (p , q) = suc p ℕ.+ q , q

fraction : ℚ → (ℕ × ℕ)
fraction = foldr-bits zer one (0 , 0)

⟦_⇓⟧ : ℚ → F.ℚ
⟦ 1ℚ ⇓⟧ = ⁺ 0 F./suc 0
⟦ lℚ xs ⇓⟧ = let n , d = fraction xs in ⁻suc n /suc d
⟦ rℚ xs ⇓⟧ = let n , d = fraction xs in ⁺ (suc n) /suc d

⟦_⇑⟧ : F.ℚ → ℚ
⟦ ⁺ zero /suc den-pred ⇑⟧ = 1ℚ
⟦ ⁺ (suc x) /suc den-pred ⇑⟧ = rℚ (normalise-suc x den-pred)
⟦ ⁻suc x /suc den-pred ⇑⟧ = lℚ (normalise-suc x den-pred)

-- open import Path.Reasoning

-- n≢sn+d : ∀ n d → (n ℕ.≡ᴮ suc (n ℕ.+ d)) ≡ false
-- n≢sn+d zero d = refl
-- n≢sn+d (suc n) d = n≢sn+d n d

-- n<sn+d : ∀ n d → (n ℕ.<ᴮ suc (n ℕ.+ d)) ≡ true
-- n<sn+d zero d = refl
-- n<sn+d (suc n) d = n<sn+d n d

-- n+d-n≡d : ∀ n d → n ℕ.+ d ℕ.∸ n ≡ d
-- n+d-n≡d zero d = refl
-- n+d-n≡d (suc n) d = n+d-n≡d n d

-- euclidian-term-helper : ∀ n d s₁ s₂ → (n ℕ.+ d ℕ.≤ s₁) → (n ℕ.+ d ℕ.≤ s₂) → euclidian n d s₁ ≡ euclidian n d s₂
-- euclidian-term-helper zero zero zero zero p₁ p₂ = refl
-- euclidian-term-helper zero zero zero (suc s₂) p₁ p₂ = refl
-- euclidian-term-helper zero zero (suc s₁) zero p₁ p₂ = refl
-- euclidian-term-helper zero zero (suc s₁) (suc s₂) p₁ p₂ = refl
-- euclidian-term-helper zero (suc d) (suc s₁) (suc s₂) p₁ p₂ = cong lℚ (euclidian-term-helper zero d s₁ s₂ (ℕ.p≤p d s₁ p₁) (ℕ.p≤p d s₂ p₂))
-- euclidian-term-helper (suc n) zero (suc s₁) (suc s₂) p₁ p₂ = cong rℚ (euclidian-term-helper n zero s₁ s₂ (ℕ.p≤p (n ℕ.+ zero) s₁ p₁) (ℕ.p≤p (n ℕ.+ zero) s₂ p₂))
-- euclidian-term-helper (suc n) (suc d) (suc s₁) (suc s₂) p₁ p₂ with n ℕ.≡ᴮ d | n ℕ.<ᴮ d
-- euclidian-term-helper (suc n) (suc d) (suc s₁) (suc s₂) p₁ p₂ | false | false = cong rℚ (euclidian-term-helper (n ℕ.∸ suc d) (suc d) s₁ s₂ {!!} {!!})
-- euclidian-term-helper (suc n) (suc d) (suc s₁) (suc s₂) p₁ p₂ | false | true  = cong lℚ (euclidian-term-helper (suc n) (d ℕ.∸ suc n) s₁ s₂ {!!} {!!})
-- euclidian-term-helper (suc n) (suc d) (suc s₁) (suc s₂) p₁ p₂ | true  | _ = refl

-- norm-l : ∀ n d → normalise-suc n (suc n ℕ.+ d) ≡ lℚ (normalise-suc n d)
-- norm-l n d =
--   normalise-suc n (suc n ℕ.+ d) ≡⟨⟩
--   euclidian n (suc n ℕ.+ d) (n ℕ.+ (suc n ℕ.+ d)) ≡⟨ cong (euclidian n (suc n ℕ.+ d)) (ℕ.+-suc n (n ℕ.+ d)) ⟩
--   euclidian n (suc n ℕ.+ d) (suc n ℕ.+ (n ℕ.+ d)) ≡⟨⟩
--   (if n ℕ.≡ᴮ suc (n ℕ.+ d) then 1ℚ else
--        if n ℕ.<ᴮ suc (n ℕ.+ d) then lℚ (euclidian n (n ℕ.+ d ℕ.∸ n) (n ℕ.+ (n ℕ.+ d))) else rℚ (euclidian (n ℕ.∸ suc (suc (n ℕ.+ d))) (suc (n ℕ.+ d)) (n ℕ.+ (n ℕ.+ d)))) ≡⟨ cong (if_then 1ℚ else if n ℕ.<ᴮ suc (n ℕ.+ d) then lℚ (euclidian n (n ℕ.+ d ℕ.∸ n) (n ℕ.+ (n ℕ.+ d))) else rℚ (euclidian (n ℕ.∸ suc (suc (n ℕ.+ d))) (suc (n ℕ.+ d)) (n ℕ.+ (n ℕ.+ d)))) (n≢sn+d n d) ⟩
--   (if n ℕ.<ᴮ suc (n ℕ.+ d) then
--        lℚ (euclidian n (n ℕ.+ d ℕ.∸ n) (n ℕ.+ (n ℕ.+ d))) else
--        rℚ (euclidian (n ℕ.∸ suc (suc (n ℕ.+ d))) (suc (n ℕ.+ d)) (n ℕ.+ (n ℕ.+ d)))) ≡⟨ cong (if_then lℚ ((euclidian n (n ℕ.+ d ℕ.∸ n) (n ℕ.+ (n ℕ.+ d)))) else rℚ ((euclidian (n ℕ.∸ suc (suc (n ℕ.+ d))) (suc (n ℕ.+ d)) (n ℕ.+ (n ℕ.+ d))))) (n<sn+d n d) ⟩
--   lℚ (euclidian n (n ℕ.+ d ℕ.∸ n) (n ℕ.+ (n ℕ.+ d))) ≡⟨ cong (λ ndn → lℚ (euclidian n ndn (n ℕ.+ (n ℕ.+ d)))) (n+d-n≡d n d) ⟩
--   lℚ (euclidian n d (n ℕ.+ (n ℕ.+ d))) ≡⟨ {!!} ⟩
--   lℚ (euclidian n d (n ℕ.+ d)) ≡⟨⟩
--   lℚ (normalise-suc n d) ∎


-- ℚ-retract′ : ∀ x → normalise-suc (fst (fraction x)) (snd (fraction x)) ≡ x
-- ℚ-retract′ 1ℚ = refl
-- ℚ-retract′ (rℚ x) = {!!}
-- ℚ-retract′ (lℚ x) = let n , d = fraction x in
--   normalise-suc n (suc (n ℕ.+ d)) ≡⟨ {!!} ⟩
--   lℚ x ∎

-- ℚ-retract : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
-- ℚ-retract 1ℚ = refl
-- ℚ-retract (lℚ x) = cong lℚ (ℚ-retract′ x)
-- ℚ-retract (rℚ x) = cong rℚ (ℚ-retract′ x)
