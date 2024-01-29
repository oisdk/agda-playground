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
swap-lhs x y with does (x ≟ x) | why (x ≟ x)
... | true  | _ = refl
... | false | x≢x = ⊥-elim (x≢x refl)

swap-rhs : ∀ x y → x ↔ y · y ≡ x
swap-rhs x y with does (x ≟ y) | why (x ≟ y)
... | true  | x≡y = sym x≡y
... | false | _ with does (y ≟ y) | why (y ≟ y)
... | false | y≢y = ⊥-elim (y≢y refl)
... | true  | _ = refl

swap-id : ∀ x y → x ↔ x · y ≡ y
swap-id x y with does (x ≟ y) | why (x ≟ y)
... | false | _ = refl
... | true  | x≡y = x≡y

swap-neq : ∀ x y z → x ≢ z → y ≢ z → x ↔ y · z ≡ z
swap-neq x y z x≢z y≢z with does (x ≟ z) | why (x ≟ z) | does (y ≟ z) | why (y ≟ z)
... | true | x≡z | _ | _ = ⊥-elim (x≢z x≡z)
... | _ | _ | true | y≡z = ⊥-elim (y≢z y≡z)
... | false | _ | false | _ = refl

swap-com : ∀ x y z → x ↔ y · z ≡ y ↔ x · z
swap-com x y z with does (x ≟ z) | why (x ≟ z) | does (y ≟ z) | why (y ≟ z)
... | false | _   | false | _ = refl
... | false | _   | true  | _ = refl
... | true  | _   | false | _ = refl
... | true  | x≡z | true  | y≡z = y≡z ; sym x≡z
