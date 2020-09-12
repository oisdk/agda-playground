{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Dyck where

open import Prelude
open import Algebra
open import Data.Nat using (_+_)
import Data.Nat.Properties as ℕ
open import Agda.Builtin.Nat using (_-_)

record Bal : Type₀ where
  constructor _⟩⟨_
  field
    left  : ℕ
    right : ℕ
open Bal public

infix 4.5 _⟩-⟨_ _⟩⟨_ _+⟨_⟩+_ _+⟨⟩+_

_⟩-⟨_ : ℕ → ℕ → Bal
zero  ⟩-⟨ m     = zero  ⟩⟨ m
suc n ⟩-⟨ zero  = suc n ⟩⟨ zero
suc n ⟩-⟨ suc m = n ⟩-⟨ m

_+⟨_⟩+_ : ℕ → Bal → ℕ → Bal
x +⟨ z ⟩+ y = right z + x ⟩⟨ left z  + y

_+⟨⟩+_ : Bal → Bal → Bal
x +⟨⟩+ y = left x +⟨ right x ⟩-⟨ left y ⟩+ right y

mempty : Bal
mempty = 0 ⟩⟨ 0

diff-zeroʳ : ∀ n → n ⟩-⟨ zero ≡ n ⟩⟨ zero
diff-zeroʳ zero    = refl
diff-zeroʳ (suc n) = refl

invert : Bal → Bal
invert (x ⟩⟨ y) = y ⟩⟨ x

diff-inv : ∀ x y → invert (x ⟩-⟨ y) ≡ y ⟩-⟨ x
diff-inv zero  zero = refl
diff-inv zero (suc y) = refl
diff-inv (suc x) zero = refl
diff-inv (suc x) (suc y) = diff-inv x y

open import Path.Reasoning

add-inv : ∀ x y → (x +⟨⟩+ y) ≡ invert (invert y +⟨⟩+ invert x)
add-inv (xl ⟩⟨ xr) (yl ⟩⟨ yr) = cong₂ _⟩⟨_ (cong (_+ xl) (cong left (diff-inv xr yl))) (cong (_+ yr) (cong right (diff-inv xr yl)))

0+⟨⟩ : ∀ x → mempty +⟨⟩+ x ≡ x
0+⟨⟩ (zero   ⟩⟨ xr) i = zero ⟩⟨ xr
0+⟨⟩ (suc xl ⟩⟨ xr) i = suc (ℕ.+-idʳ xl i) ⟩⟨ xr

⟨⟩+0 : ∀ x → x +⟨⟩+ mempty ≡ x
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
    (xr - (right (yr ⟩-⟨ zl) + yl)) + (yr - zl) ≡˘⟨ cong₂ _+_ (diff-sub xr _) (diff-sub yr zl) ⟩
    left (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl) + left (yr ⟩-⟨ zl) ∎

  rhs : left (left (xr ⟩-⟨ yl) + yr ⟩-⟨ zl) + zr ≡ left (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl) + (left (yr ⟩-⟨ zl) + zr)
  rhs = cong (_+ zr) (rhs′ xr yl yr zl) ; ℕ.+-assoc (left (xr ⟩-⟨ right (yr ⟩-⟨ zl) + yl)) (left (yr ⟩-⟨ zl)) zr

semigroupBal : Semigroup _
semigroupBal .Semigroup.𝑆 = Bal
semigroupBal .Semigroup._∙_ = _+⟨⟩+_
semigroupBal .Semigroup.assoc = ⟨⟩-assoc

monoidBal : Monoid _
Monoid.𝑆 monoidBal = Bal
Monoid._∙_ monoidBal = _+⟨⟩+_
Monoid.ε monoidBal = mempty
Monoid.assoc monoidBal = ⟨⟩-assoc
Monoid.ε∙ monoidBal = 0+⟨⟩
Monoid.∙ε monoidBal = ⟨⟩+0
