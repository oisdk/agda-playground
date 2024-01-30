{-# OPTIONS --cubical --safe #-}

module Data.Nat.Properties where

open import Data.Nat.Base
open import Agda.Builtin.Nat using () renaming (_<_ to _<ᴮ_) public
open import Prelude
open import Cubical.Data.Nat using (caseNat; injSuc) public
open import Data.Nat.DivMod

infixr 4 _⊔_ _-1⊔_

_⊔_ _-1⊔_ : ℕ → ℕ → ℕ

zero  ⊔ m = m
suc n ⊔ m = suc (m -1⊔ n)

zero  -1⊔ n = n
suc m -1⊔ n = n ⊔ m


znots : ∀ {n} → zero ≢ suc n
znots z≡s = subst (caseNat ⊤ ⊥) z≡s tt

snotz : ∀ {n} → suc n ≢ zero
snotz s≡z = subst (caseNat ⊥ ⊤) s≡z tt

pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero

suc-inj : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-inj = cong pred

+-inj : ∀ x {n m} → x + n ≡ x + m → n ≡ m
+-inj zero p = p
+-inj (suc x) p = +-inj x (suc-inj p)

open import Relation.Nullary.Discrete.FromBoolean

module Eqℕ where
  open import Agda.Builtin.Nat using () renaming (_==_ to _≡ᴮ_) public

  sound : ∀ n m →  T (n ≡ᴮ m) → n ≡ m
  sound zero zero p i = zero
  sound (suc n) (suc m) p i = suc (sound n m p i)

  complete : ∀ n → T (n ≡ᴮ n)
  complete zero = tt
  complete (suc n) = complete n

discreteℕ : Discrete ℕ
discreteℕ = from-bool-eq (record { Eqℕ })

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-idʳ : ∀ x → x + 0 ≡ x
+-idʳ zero     = refl
+-idʳ (suc x)  = cong suc (+-idʳ x)

+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero = +-idʳ x
+-comm x (suc y) = +-suc x y ; cong suc (+-comm x y)

infix 4 _<_
_<_ : ℕ → ℕ → Type
n < m = T (n <ᴮ m)

infix 4 _≤ᴮ_
_≤ᴮ_ : ℕ → ℕ → Bool
n ≤ᴮ m = not (m <ᴮ n)

infix 4 _≤_
_≤_ : ℕ → ℕ → Type
n ≤ m = T (n ≤ᴮ m)

infix 4 _≥ᴮ_
_≥ᴮ_ : ℕ → ℕ → Bool
_≥ᴮ_ = flip _≤ᴮ_

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc zero     y z i = y + z
+-assoc (suc x)  y z i = suc (+-assoc x y z i)

+-*-distrib : ∀ x y z → (x + y) * z ≡ x * z + y * z
+-*-distrib zero y z = refl
+-*-distrib (suc x) y z = cong (z +_) (+-*-distrib x y z) ; sym (+-assoc z (x * z) (y * z))

*-zeroʳ : ∀ x → x * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc x) = *-zeroʳ x

*-suc : ∀ x y → x + x * y ≡ x * suc y
*-suc zero    y = refl
*-suc (suc x) y = cong suc (sym (+-assoc x y (x * y)) ; cong (_+ x * y) (+-comm x y) ; +-assoc y x (x * y) ; cong (y +_) (*-suc x y))

*-comm : ∀ x y → x * y ≡ y * x
*-comm zero    y = sym (*-zeroʳ y)
*-comm (suc x) y = cong (y +_) (*-comm x y) ; *-suc y x

*-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
*-assoc zero    y z = refl
*-assoc (suc x) y z = +-*-distrib y (x * y) z ; cong (y * z +_) (*-assoc x y z)

open import Data.Nat.DivMod
open import Agda.Builtin.Nat using (div-helper)

div-helper′ : (m n j : ℕ) → ℕ
div-helper′ m  zero    j      = zero
div-helper′ m (suc n)  zero   = suc (div-helper′ m n m)
div-helper′ m (suc n) (suc j) = div-helper′ m n j

div-helper-lemma : ∀ k m n j → div-helper k m n j ≡ k + div-helper′ m n j
div-helper-lemma k m zero j = sym (+-idʳ k)
div-helper-lemma k m (suc n) zero = div-helper-lemma (suc k) m n m ; sym (+-suc k (div-helper′ m n m))
div-helper-lemma k m (suc n) (suc j) = div-helper-lemma k m n j

Even : ℕ → Type
Even n = T (even n)

open Eqℕ using (_≡ᴮ_)

odd : ℕ → Bool
odd n = not (rem n 2 ≡ᴮ 0)

Odd : ℕ → Type
Odd n = T (odd n)

s≤s : ∀ n m → n ≤ m → suc n ≤ suc m
s≤s zero m p = tt
s≤s (suc n) m p = p

n≤s : ∀ n m → n ≤ m → n ≤ suc m
n≤s zero m p = tt
n≤s (suc zero) m p = tt
n≤s (suc (suc n)) zero p = p
n≤s (suc (suc n₁)) (suc n) p = n≤s (suc n₁) n p

div-≤ : ∀ n m → n ÷ suc m ≤ n
div-≤ n m = subst (_≤ n) (sym (div-helper-lemma 0 m n m)) (go m n m)
  where
  go : ∀ m n j → div-helper′ m n j ≤ n
  go m zero j = tt
  go m (suc n) zero = s≤s (div-helper′ m n m) n (go m n m)
  go m (suc n) (suc j) = n≤s (div-helper′ m n j) n (go m n j)

≤-trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
≤-trans zero y z p q = tt
≤-trans (suc n) zero zero p q = p
≤-trans (suc zero) zero (suc n) p q = tt
≤-trans (suc (suc n₁)) zero (suc n) p q = ≤-trans (suc n₁) zero n p tt
≤-trans (suc n) (suc zero) zero p q = q
≤-trans (suc zero) (suc zero) (suc n) p q = tt
≤-trans (suc (suc n₁)) (suc zero) (suc n) p q = ≤-trans (suc n₁) zero n p tt
≤-trans (suc n₁) (suc (suc n)) zero p q = q
≤-trans (suc zero) (suc (suc n₁)) (suc n) p q = tt
≤-trans (suc (suc n₁)) (suc (suc n₂)) (suc n) p q = ≤-trans (suc n₁) (suc n₂) n p q

p≤n : ∀ n m → suc n ≤ m → n ≤ m
p≤n zero m p = tt
p≤n (suc n) zero p = p
p≤n (suc zero) (suc n) p = tt
p≤n (suc (suc n₁)) (suc n) p = p≤n (suc n₁) n p

p≤p : ∀ n m → suc n ≤ suc m → n ≤ m
p≤p zero m p = tt
p≤p (suc n) m p = p

≤-refl : ∀ n → n ≤ n
≤-refl zero = tt
≤-refl (suc zero) = tt
≤-refl (suc (suc n)) = ≤-refl (suc n)

linearise : ∀ n m → n ≡ m → n ≡ m
linearise n m n≡m with discreteℕ n m
... | yes p = p
... | no ¬p = ⊥-elim (¬p n≡m)

x≢sx+y : ∀ x y → x ≢ suc x + y
x≢sx+y zero y = znots
x≢sx+y (suc x) y p = x≢sx+y x y (suc-inj p)
