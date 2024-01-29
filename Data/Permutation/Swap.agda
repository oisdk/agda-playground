{-# OPTIONS --safe #-}

open import Prelude hiding (_↔_)

module Data.Permutation.Swap (_≟_ : Discrete A) where

infixr 4.5 _↔_·_
_↔_·_ : A → A → A → A
x ↔ y · z =
  if does (x ≟ z) then y else
  if does (y ≟ z) then x else
  z

swap-lhs : ∀ x y → x ↔ y · x ≡ y
swap-lhs x y = cong (bool′ _ _) (it-does (x ≟ x) refl)

swap-rhs : ∀ x y → x ↔ y · y ≡ x
swap-rhs x y with does (x ≟ y) | why (x ≟ y)
... | true  | x≡y = sym x≡y
... | false | _   = cong (bool′ _ _) (it-does (y ≟ y) refl)

swap-id : ∀ x y → x ↔ x · y ≡ y
swap-id x y with does (x ≟ y) | why (x ≟ y)
... | false | _ = refl
... | true  | x≡y = x≡y

swap-neq : ∀ x y z → x ≢ z → y ≢ z → x ↔ y · z ≡ z
swap-neq x y z x≢z y≢z = cong (bool′ _ _) (it-doesn't (x ≟ z) x≢z) ; cong (bool′ _ _) (it-doesn't (y ≟ z) y≢z)

swap-com : ∀ x y z → x ↔ y · z ≡ y ↔ x · z
swap-com x y z with does (x ≟ z) | why (x ≟ z) | does (y ≟ z) | why (y ≟ z)
... | false | _   | false | _ = refl
... | false | _   | true  | _ = refl
... | true  | _   | false | _ = refl
... | true  | x≡z | true  | y≡z = y≡z ; sym x≡z

swap-dup : ∀ x y z → x ↔ y · x ↔ y · z ≡ z
swap-dup x y z with does (x ≟ z) | why (x ≟ z) | does (y ≟ z) | why (y ≟ z)
... | false | x≢z | false | y≢z = cong (bool′ _ _) (it-doesn't (x ≟ z) x≢z) ; cong (bool′ _ _) (it-doesn't (y ≟ z) y≢z)
... | true  | x≡z | true  | y≡z = cong (bool′ _ _) (it-does (x ≟ y) (x≡z ; sym y≡z)) ; y≡z
... | true  | x≡z | false | y≢z = cong (bool′ _ _) (it-doesn't (x ≟ y) (y≢z ∘ sym ∘ (sym x≡z ;_))) ; cong (bool′ _ _) (it-does (y ≟ y) refl) ; x≡z
... | false | x≢z | true  | y≡z = cong (bool′ _ _) (it-does (x ≟ x) refl) ; y≡z
