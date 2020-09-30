{-# OPTIONS --cubical --safe #-}

module Data.Nat.Properties where

open import Data.Nat.Base
open import Agda.Builtin.Nat using () renaming (_<_ to _<ᴮ_; _==_ to _≡ᴮ_) public
open import Prelude
open import Cubical.Data.Nat using (caseNat; znots; snotz; injSuc) public

pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero

sound-== : ∀ n m →  T (n ≡ᴮ m) → n ≡ m
sound-== zero zero p i = zero
sound-== (suc n) (suc m) p i = suc (sound-== n m p i)

complete-== : ∀ n → T (n ≡ᴮ n)
complete-== zero = tt
complete-== (suc n) = complete-== n

open import Relation.Nullary.Discrete.FromBoolean

discreteℕ : Discrete ℕ
discreteℕ = from-bool-eq _≡ᴮ_ sound-== complete-==

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
_<_ : ℕ → ℕ → Type₀
n < m = T (n <ᴮ m)

infix 4 _≤ᴮ_
_≤ᴮ_ : ℕ → ℕ → Bool
zero  ≤ᴮ m = true
suc n ≤ᴮ m = n <ᴮ m

infix 4 _≤_
_≤_ : ℕ → ℕ → Type₀
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
