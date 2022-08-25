{-# OPTIONS --cubical --safe #-}

-- This module defines the Dyck monoid, also known as the bicyclic semigroup.
-- This can be used for parsing balanced parentheses.

module Algebra.Construct.Dyck where

open import Prelude
open import Algebra
open import Data.Nat using (_+_)
import Data.Nat.Properties as ℕ
open import Agda.Builtin.Nat using (_-_)

--------------------------------------------------------------------------------
-- Definition
--------------------------------------------------------------------------------

-- This type can be used to parse balanced parentheses.
-- The two ℕs represent the number of outward-facing parentheses
-- in the parse.
-- i.e.:
--
--   parse ")("        = 1 ⟩⟨ 1
--   parse "()"        = 0 ⟩⟨ 0
--   parse "()(("      = 0 ⟩⟨ 2
--   parse ")()(("     = 1 ⟩⟨ 2
--   parse ")(())(("   = 1 ⟩⟨ 2
--   parse ")(())()((" = 1 ⟩⟨ 2
record Bal : Type where
  constructor _⟩⟨_
  field
    left  : ℕ
    right : ℕ
open Bal public

infix 4.5 _⟩-⟨_ _⟩⟨_ _+⟨_⟩+_ _+⟨⟩+_

--------------------------------------------------------------------------------
-- Monoid operations
--------------------------------------------------------------------------------

-- Find the absolute difference of two numbers.
_⟩-⟨_ : ℕ → ℕ → Bal
n ⟩-⟨ m =
  if n ℕ.<ᴮ m
  then zero ⟩⟨ m - n
  else n - m ⟩⟨ zero

_+⟨_⟩+_ : ℕ → Bal → ℕ → Bal
x +⟨ zˡ ⟩⟨ zʳ ⟩+ y = zʳ + x ⟩⟨ zˡ  + y

-- The actual monoid operator
_+⟨⟩+_ : Bal → Bal → Bal
(xˡ ⟩⟨ xʳ) +⟨⟩+ (yˡ ⟩⟨ yʳ) = xˡ +⟨ xʳ ⟩-⟨ yˡ ⟩+ yʳ

-- The mempty
⟨⟩ : Bal
⟨⟩ = 0 ⟩⟨ 0

invert : Bal → Bal
invert (x ⟩⟨ y) = y ⟩⟨ x

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

diff-zeroʳ : ∀ n → n ⟩-⟨ zero ≡ n ⟩⟨ zero
diff-zeroʳ zero    = refl
diff-zeroʳ (suc n) = refl
diff-inv : ∀ x y → invert (x ⟩-⟨ y) ≡ y ⟩-⟨ x
diff-inv zero  zero = refl
diff-inv zero (suc y) = refl
diff-inv (suc x) zero = refl
diff-inv (suc x) (suc y) = diff-inv x y

open import Path.Reasoning

add-inv : ∀ x y → (x +⟨⟩+ y) ≡ invert (invert y +⟨⟩+ invert x)
add-inv (xl ⟩⟨ xr) (yl ⟩⟨ yr) = cong₂ _⟩⟨_ (cong (_+ xl) (cong left (diff-inv xr yl))) (cong (_+ yr) (cong right (diff-inv xr yl)))

0+⟨⟩ : ∀ x → ⟨⟩ +⟨⟩+ x ≡ x
0+⟨⟩ (zero   ⟩⟨ xr) i = zero ⟩⟨ xr
0+⟨⟩ (suc xl ⟩⟨ xr) i = suc (ℕ.+-idʳ xl i) ⟩⟨ xr

⟨⟩+0 : ∀ x → x +⟨⟩+ ⟨⟩ ≡ x
⟨⟩+0 (xl ⟩⟨ zero  ) i = xl ⟩⟨ zero
⟨⟩+0 (xl ⟩⟨ suc xr) i = xl ⟩⟨ suc (ℕ.+-idʳ xr i)

diff-sub : ∀ x y → left (x ⟩-⟨ y) ≡ x - y
diff-sub zero zero = refl
diff-sub zero (suc y) = refl
diff-sub (suc x) zero = refl
diff-sub (suc x) (suc y) = diff-sub x y

diff-subʳ : ∀ x y → right (x ⟩-⟨ y) ≡ y - x
diff-subʳ zero zero = refl
diff-subʳ zero (suc y) = refl
diff-subʳ (suc x) zero = refl
diff-subʳ (suc x) (suc y) = diff-subʳ x y

minus-plus : ∀ x y z → x - y - z ≡ x - (y + z)
minus-plus x zero z = refl
minus-plus zero (suc y) zero = refl
minus-plus zero (suc y) (suc z) = refl
minus-plus (suc x) (suc y) z = minus-plus x y z

lhs″ : ∀ zl xr yl yr → (zl - ((xr - yl) + yr)) + (yl - xr) ≡ ((zl - yr) + yl) - xr
lhs″ zl zero zero yr = refl
lhs″ zl zero (suc yl) yr = refl
lhs″ zl (suc xr) zero yr = ℕ.+-idʳ _ ; (cong (zl -_) (ℕ.+-comm (suc xr) yr) ; sym (minus-plus zl yr (suc xr))) ; sym (cong (_- suc xr) (ℕ.+-idʳ (zl - yr)))
lhs″ zero (suc xr) (suc yl) zero = lhs″ zero xr yl zero
lhs″ zero (suc xr) (suc yl) (suc yr) = lhs″ zero xr yl (suc yr)
lhs″ (suc zl) (suc xr) (suc yl) zero = lhs″ (suc zl) xr yl zero ; cong (_- xr) (sym (ℕ.+-suc zl yl))
lhs″ (suc zl) (suc xr) (suc yl) (suc yr) = cong (_+ (yl - xr)) (cong (suc zl -_) (ℕ.+-suc (xr - yl) yr)) ; lhs″ zl (suc xr) (suc yl) yr

rhs‴ : ∀ x y z → x + y - z ≡ x - (z - y) + (y - z)
rhs‴ zero zero zero = refl
rhs‴ zero zero (suc z) = refl
rhs‴ zero (suc y) zero = refl
rhs‴ (suc x) zero zero = refl
rhs‴ (suc x) (suc y) zero = refl
rhs‴ zero (suc y) (suc z) = rhs‴ zero y z
rhs‴ (suc x) zero (suc z) = cong (_- z) (ℕ.+-idʳ x) ; sym (ℕ.+-idʳ (x - z))
rhs‴ (suc x) (suc y) (suc z) = cong (_- z) (ℕ.+-suc x y) ; rhs‴ (suc x) y z

rhs″ : ∀ xr yl yr zl → ((xr - yl) + yr) - zl ≡ xr - (zl - yr + yl) + (yr - zl)
rhs″ (suc xr) (suc yl) yr zl = rhs″ xr yl yr zl ; cong (λ zy → suc xr - zy + (yr - zl)) (sym (ℕ.+-suc (zl - yr) yl))
rhs″ zero zero zero zero = refl
rhs″ zero zero zero (suc zl) = refl
rhs″ zero zero (suc yr) zero = refl
rhs″ zero zero (suc yr) (suc zl) = rhs″ zero zero yr zl
rhs″ zero (suc yl) zero zero = refl
rhs″ zero (suc yl) zero (suc zl) = refl
rhs″ zero (suc yl) (suc yr) zero = refl
rhs″ zero (suc yl) (suc yr) (suc zl) = rhs″ zero (suc yl) yr zl
rhs″ (suc xr) zero zero zero = refl
rhs″ (suc xr) zero (suc yr) zero = refl
rhs″ (suc xr) zero zero     (suc zl) = cong (_- zl) (ℕ.+-idʳ xr) ; cong (xr -_) (sym (ℕ.+-idʳ zl)) ; sym (ℕ.+-idʳ (xr - (zl + zero)))
rhs″ (suc xr) zero (suc yr) (suc zl) = cong (_- zl) (ℕ.+-suc xr yr) ;  rhs‴ (suc xr) yr zl ; sym (cong (λ zy → suc xr - zy + (yr - zl)) (ℕ.+-idʳ (zl - yr)))

⟨⟩-assoc : Associative _+⟨⟩+_
⟨⟩-assoc (xl ⟩⟨ xr ) (yl ⟩⟨ yr ) (zl ⟩⟨ zr) = cong₂ _⟩⟨_ lhs rhs
  where

  lhs′ : ∀ xr yl yr zl → right (left (xr ⟩-⟨ yl) + yr ⟩-⟨ zl) + right (xr ⟩-⟨ yl) ≡ right (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl)
  lhs′ xr yl yr zl =
    right (left (xr ⟩-⟨ yl) + yr ⟩-⟨ zl) + right (xr ⟩-⟨ yl) ≡⟨ cong₂ _+_ (diff-subʳ (left (xr ⟩-⟨ yl) + yr) zl) (diff-subʳ xr yl) ⟩
    (zl - (left (xr ⟩-⟨ yl) + yr)) + (yl - xr) ≡⟨ cong (λ xy → (zl - (xy + yr)) + (yl - xr)) (diff-sub xr yl) ⟩
    (zl - ((xr - yl) + yr)) + (yl - xr) ≡⟨ lhs″ zl xr yl yr ⟩
    ((zl - yr) + yl) - xr ≡˘⟨ cong (λ yz → (yz + yl) - xr) (diff-subʳ yr zl) ⟩
    (right (yr ⟩-⟨ zl) + yl) - xr ≡˘⟨ diff-subʳ xr _ ⟩
    right (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl) ∎

  lhs : right (left (xr ⟩-⟨ yl) + yr ⟩-⟨ zl) + (right (xr ⟩-⟨ yl) + xl) ≡ right (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl) + xl
  lhs = sym (ℕ.+-assoc _ (right (xr ⟩-⟨ yl)) xl) ; cong (_+ xl) (lhs′ xr yl yr zl)

  rhs′ : ∀ xr yl yr zl → left (left (xr ⟩-⟨ yl) + yr ⟩-⟨ zl) ≡ left (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl) + left (yr ⟩-⟨ zl)
  rhs′ xr yl yr zl =
    left (left (xr ⟩-⟨ yl) + yr ⟩-⟨ zl) ≡⟨ diff-sub _ zl ⟩
    left (xr ⟩-⟨ yl) + yr - zl ≡⟨ cong (_- zl) (cong (_+ yr) (diff-sub xr yl)) ⟩
    (xr - yl) + yr - zl ≡⟨ rhs″ xr yl yr zl ⟩
    (xr - ((zl - yr) + yl)) + (yr - zl) ≡˘⟨ cong (λ yz → (xr - (yz + yl)) + (yr - zl)) (diff-subʳ yr zl) ⟩
    (xr - (right (yr ⟩-⟨ zl) + yl)) + (yr - zl) ≡˘⟨ cong₂ _+_ (diff-sub xr (right (yr ⟩-⟨ zl) + yl)) (diff-sub yr zl) ⟩
    left (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl) + left (yr ⟩-⟨ zl) ∎

  rhs : left (left (xr ⟩-⟨ yl) + yr ⟩-⟨ zl) + zr ≡ left (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl) + (left (yr ⟩-⟨ zl) + zr)
  rhs = cong (_+ zr) (rhs′ xr yl yr zl) ; ℕ.+-assoc (left (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl)) (left (yr ⟩-⟨ zl)) zr

semigroupBal : Semigroup Bal
semigroupBal .Semigroup._∙_ = _+⟨⟩+_
semigroupBal .Semigroup.assoc = ⟨⟩-assoc

monoidBal : Monoid Bal
Monoid._∙_ monoidBal = _+⟨⟩+_
Monoid.ε monoidBal = ⟨⟩
Monoid.assoc monoidBal = ⟨⟩-assoc
Monoid.ε∙ monoidBal = 0+⟨⟩
Monoid.∙ε monoidBal = ⟨⟩+0
