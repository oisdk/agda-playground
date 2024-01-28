{-# OPTIONS --allow-unsolved-metas #-}

module Data.Permutation where

open import Prelude hiding (_↔_)
open import Data.List
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Data.List.Properties

--------------------------------------------------------------------------------
-- Unnormalised Representation
--------------------------------------------------------------------------------

Swaps : Type
Swaps = List (ℕ × ℕ)

infixr 4.5 _↔_·_
_↔_·_ : ℕ → ℕ → ℕ → ℕ
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

infixr 4.5 _·_
_·_ : Swaps → ℕ → ℕ
_·_ = flip (foldl (flip (uncurry _↔_·_)))

--------------------------------------------------------------------------------
-- Normalised Representation
--------------------------------------------------------------------------------

Diffs : Type
Diffs = List (ℕ × ℕ)

unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
unflatten-alg x y k n = ((n + x) , suc (n + x + y)) ∷ k (suc n + x)

[_]↑ : Diffs → Swaps
[ xs ]↑ = foldr (uncurry unflatten-alg) (const []) xs 0

infixr 4.5 _↔′_·_
_↔′_·_ : ℕ → ℕ → ℕ → ℕ
zero  ↔′ zero  · z     = z
zero  ↔′ y     · zero  = y
zero  ↔′ suc y · suc z = if does (y ≟ z) then zero else suc z
x     ↔′ zero  · zero  = x
suc x ↔′ suc y · zero  = zero
suc x ↔′ zero  · suc z = if does (x ≟ z) then zero else suc z
suc x ↔′ suc y · suc z = suc (x ↔′ y · z)

swap-suc : ∀ x y z → suc x ↔ suc y · suc z ≡ suc (x ↔ y · z)
swap-suc x y z with does (x ≟ z)
... | true = refl
... | false with does (y ≟ z)
... | false = refl
... | true = refl

swap-swap′ : ∀ x y z → x ↔ y · z ≡ x ↔′ y · z
swap-swap′ zero    zero    z       = swap-id zero z
swap-swap′ zero    (suc y) zero    = refl
swap-swap′ zero    (suc y) (suc z) = refl
swap-swap′ (suc x) zero    zero    = refl
swap-swap′ (suc x) (suc y) zero    = refl
swap-swap′ (suc x) zero    (suc z) = refl
swap-swap′ (suc x) (suc y) (suc z) = swap-suc x y z ; cong suc (swap-swap′ x y z)

perm-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
perm-alg zero    y k zero    = suc (k y)
perm-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
perm-alg (suc x) y k zero    = zero
perm-alg (suc x) y k (suc z) = suc (perm-alg x y k z)


infixr 4.5 _⊙_
_⊙_ : Diffs → ℕ → ℕ
_⊙_ = foldr (uncurry perm-alg) id

infixr 4.5 _↔_⊙_
_↔_⊙_ : ℕ → ℕ → ℕ → ℕ
_↔_⊙_ x y = perm-alg x y id

perm-alg-swap : ∀ x y z → x ↔ y ⊙ z ≡ x ↔′ suc (x + y) · z
perm-alg-swap zero y zero = refl
perm-alg-swap zero y (suc z) = refl
perm-alg-swap (suc x) y zero = refl
perm-alg-swap (suc x) y (suc z) = cong suc (perm-alg-swap x y z)

shift : ℕ → Diffs → Diffs
shift m [] = []
shift m ((x , y) ∷ xs) = (m + x , y) ∷ xs

perm-alg-com : ∀ x y xs z → (x , y) ∷ xs ⊙ z ≡ shift (suc x) xs ⊙ x ↔ y ⊙ z
perm-alg-com x y [] z = refl
perm-alg-com zero y (w ∷ xs) zero = refl
perm-alg-com (suc x) y (w ∷ xs) zero = refl
perm-alg-com (suc x) y (w ∷ xs) (suc z) = cong suc (perm-alg-com x y (w ∷ xs) z)
perm-alg-com zero y (w ∷ xs) (suc z) with does (y ≟ z)
... | false = refl
... | true  = refl

swap-unf-alg : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
swap-unf-alg x y k m n = k (suc m + x) (m + x ↔ suc (m + x + y) · n)

swap-unf′ : Swaps → ℕ → ℕ → ℕ
swap-unf′ = foldr (uncurry swap-unf-alg) (const id)

swap-shift : ∀ m n xs → shift m xs ⊙ n ≡ swap-unf′ xs m n
swap-shift m n [] = refl
swap-shift m n ((x , y) ∷ xs) =
  perm-alg (m + x) y (_⊙_ xs) n
    ≡⟨ perm-alg-com (m + x) y xs n ⟩
  shift (suc m + x) xs ⊙ perm-alg (m + x) y id n
    ≡⟨ cong (_⊙_ (shift (suc m + x) xs)) (perm-alg-swap (m + x) y n) ⟩
  shift (suc m + x) xs ⊙ m + x ↔′ suc (m + x + y) · n
    ≡˘⟨ cong (_⊙_ (shift (suc m + x) xs)) (swap-swap′ (m + x) _ n) ⟩
  shift (suc m + x) xs ⊙ m + x ↔ suc (m + x + y) · n
    ≡⟨ swap-shift (suc m + x) _ xs ⟩
  swap-unf′ xs (suc m + x) (m + x ↔ suc (m + x + y) · n)
    ≡⟨⟩
  swap-unf-alg x y (swap-unf′ xs) m n ∎

shift-0 : ∀ xs → shift 0 xs ≡ xs
shift-0 [] = refl
shift-0 (x ∷ xs) = refl


swaps-compress : ∀ xs n → xs ⊙ n ≡ [ xs ]↑ · n
swaps-compress xs n =
  xs ⊙ n
    ≡˘⟨ cong (_⊙ n) (shift-0 xs) ⟩
  shift 0 xs ⊙ n
    ≡⟨ swap-shift 0 n xs ⟩
  swap-unf′ xs 0 n
    ≡˘⟨ cong′ {A = ℕ → ℕ → ℕ} (λ e → e 0 n) (foldr-fusion (λ xs m n → foldl-by-r (flip (uncurry _↔_·_)) n (xs m)) (const []) (λ _ _ → refl) xs) ⟩
  foldl-by-r (flip (uncurry _↔_·_)) n [ xs ]↑
    ≡˘⟨ foldl-is-foldr (flip (uncurry _↔_·_)) n [ xs ]↑ ⟩
  [ xs ]↑ · n ∎
  
max-num-alg : ℕ × ℕ → ℕ → ℕ
max-num-alg (x , y) z = suc (x + (y ⊔ z))

max-num : Diffs → ℕ
max-num = foldr max-num-alg zero

open import Data.Maybe using (mapMaybe)

cmp-diff : ℕ → ℕ → Maybe (Bool × ℕ)
cmp-diff zero zero = nothing
cmp-diff zero (suc y) = just (false , y)
cmp-diff (suc x) zero = just (true  , x)
cmp-diff (suc x) (suc y) = cmp-diff x y

swap-diff : ℕ → ℕ → Maybe (ℕ × ℕ)
swap-diff x y = mapMaybe (map₁ (bool′ x y)) (cmp-diff x y)

cmp-reflect : ℕ → ℕ → Maybe (Bool × ℕ) → Type
cmp-reflect x y (just (false , z)) = suc x + z ≡ y
cmp-reflect x y (just (true  , z)) = suc y + z ≡ x
cmp-reflect x y nothing = x ≡ y

suc-reflect : ∀ x y z → cmp-reflect x y z → cmp-reflect (suc x) (suc y) z
suc-reflect x y (just (false , r)) p = cong suc p
suc-reflect x y (just (true , r)) p = cong suc p
suc-reflect x y nothing p = cong suc p

cmp-reflects : ∀ x y → cmp-reflect x y (cmp-diff x y)
cmp-reflects zero zero = refl
cmp-reflects zero (suc y) = refl
cmp-reflects (suc x) zero = refl
cmp-reflects (suc x) (suc y) = suc-reflect x y (cmp-diff x y) (cmp-reflects x y)

infixr 5 _∷ₚ_
_∷ₚ_ : ℕ × ℕ → Diffs → Diffs
x ∷ₚ [] = x ∷ []
(xₛ , xₜ) ∷ₚ ((yₛ , yₜ) ∷ xs) = case cmp-diff xₛ yₛ of
  λ { nothing → maybe (shift (suc xₛ) xs) (λ lg → (xₛ , yₜ) ∷ lg ∷ₚ xs) (swap-diff xₜ yₜ)
    ; (just (false , yₛ)) → (xₛ , xₜ) ∷ (yₛ , yₜ) ∷ xs
    ; (just (true  , xₛ)) → (yₛ , xₛ ↔ xₜ ⊙ yₜ) ∷ (xₛ , xₜ) ∷ₚ xs
    }

[_]↓ : Swaps → Diffs
[_]↓ = foldr _∷ₚ_ [] ∘ catMaybes (uncurry swap-diff)

--
--


perm-alg-dup : ∀ x y z → x ↔ y ⊙ x ↔ y ⊙ z ≡ z
perm-alg-dup zero y zero with does (y ≟ y) | why (y ≟ y)
perm-alg-dup zero y zero | false | y≢y = ⊥-elim (y≢y refl)
perm-alg-dup zero y zero | true | _ = refl
perm-alg-dup (suc x) y zero = refl
perm-alg-dup (suc x) y (suc z) = cong suc (perm-alg-dup x y z)
perm-alg-dup zero y (suc z) with does (y ≟ z) | why (y ≟ z)
... | true  | y≡z = cong suc y≡z
... | false | y≢z with does (y ≟ z) | why (y ≟ z)
... | true | y≡z = ⊥-elim (y≢z y≡z)
... | false | _ = refl


cons-swap : ∀ x y xs z → (x , y) ∷ₚ xs ⊙ z ≡ xs ⊙ x ↔ y ⊙ z
cons-swap₁ : ∀ x k y z xs n → (x , k ↔ y ⊙ z) ∷ (k , y) ∷ₚ xs ⊙ n ≡ (x , z) ∷ xs ⊙ suc (x + k) ↔ y ⊙ n

cons-swap₁ (suc x) k y z xs (suc n) = cong suc (cons-swap₁ x k y z xs n)
cons-swap₁ (suc x) k y z xs zero = refl
cons-swap₁ zero k y z xs zero = cong suc (cons-swap k y xs (perm-alg k y id z) ; cong (xs ⊙_) (perm-alg-dup k y z))
cons-swap₁ zero k y z xs (suc n) with does (k ↔ y ⊙ z ≟ n) | does (z ≟ k ↔ y ⊙ n) | why (k ↔ y ⊙ z ≟ n) | why (z ≟ k ↔ y ⊙ n)
... | false | false | _ | _ = cong suc (cons-swap k y xs n) 
... | true  | true  | _ | _ = refl
... | false | true  | e1 | e2 = ⊥-elim (e1 (cong (perm-alg k y id) e2 ; perm-alg-dup k y n))
... | true  | false | e1 | e2 = ⊥-elim (e2 (sym (cong (perm-alg k y id) (sym e1) ; perm-alg-dup k y z)))

cons-swap₂ : ∀ x y xs z n → (x , y) ∷ (y , z) ∷ₚ xs ⊙ n ≡ (x , y) ∷ xs ⊙ x ↔ suc (y + z) ⊙ n
cons-swap₂ (suc x) y xs z zero = refl
cons-swap₂ (suc x) y xs z (suc n) = cong suc (cons-swap₂ x y xs z n)
cons-swap₂ zero y xs z zero with does (y ≟ suc (y + z)) | why (y ≟ suc (y + z))
... | false | p = cong suc $
  (y , z) ∷ₚ xs ⊙ y ≡⟨ cons-swap y z xs y ⟩
  xs ⊙ (y ↔ z ⊙ y) ≡⟨ cong (xs ⊙_) (perm-alg-swap y z y ; sym (swap-swap′ y (suc (y + z)) y) ; swap-lhs y (suc (y + z)) ) ⟩
  xs ⊙ suc (y + z) ∎
... | true  | p = ⊥-elim (x≢sx+y y z p)
cons-swap₂ zero y xs z (suc n) with does (y ≟ n) | why (y ≟ n) | does (suc (y + z) ≟ n) | why (suc (y + z) ≟ n)
cons-swap₂ zero y xs z (suc n) | true | ynp | true | synp = ⊥-elim (x≢sx+y n z (sym synp ; cong suc (cong (_+ z) ynp)))
cons-swap₂ zero y xs z (suc n) | false | ynp | true | synp = cong suc (cons-swap y z xs n ; cong (xs ⊙_) (perm-alg-swap y z n ; sym (swap-swap′ y _ n) ; cong (y ↔_· n) synp ; swap-rhs y n))
cons-swap₂ zero y xs z (suc n) | yn | ynp | false | synp with does (y ≟ n) | why (y ≟ n)
cons-swap₂ zero y xs z (suc n) | false | ynp | false | synp | true | ynp′ = ⊥-elim (ynp ynp′)
cons-swap₂ zero y xs z (suc n) | true | ynp | false | synp | false | ynp′ = ⊥-elim (ynp′ ynp)
cons-swap₂ zero y xs z (suc n) | true | ynp | false | synp | true | ynp′ = refl
cons-swap₂ zero y xs z (suc n) | false | ynp | false | synp | false | ynp′ = cong suc (cons-swap y z xs n ; cong (xs ⊙_) (perm-alg-swap y z n ; sym (swap-swap′ y _ n) ; swap-neq y _ n ynp synp))

-- perm-alg-com : ∀ x y xs z → (x , y) ∷ xs ⊙ z ≡ shift (suc x) xs ⊙ x ↔ y ⊙ z
-- 
-- perm-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
-- perm-alg zero    y k zero    = suc (k y)
-- perm-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
-- perm-alg (suc x) y k zero    = zero
-- perm-alg (suc x) y k (suc z) = suc (perm-alg x y k z)
--
doesn't : ¬ A → (d : Dec A) → does d ≡ false
doesn't ¬A (no why₁) = refl
doesn't ¬A (yes A) = ⊥-elim (¬A A)

cons-swap₃ : ∀ x y z xs n → (x , suc (y + z)) ∷ (y , z) ∷ₚ xs ⊙ n ≡ (x , suc (y + z)) ∷ xs ⊙ (x ↔ y ⊙ n)
cons-swap₃ (suc x) y z xs zero = refl
cons-swap₃ (suc x) y z xs (suc n) = cong suc (cons-swap₃ x y z xs n)
cons-swap₃ zero y z xs zero =
  suc ((y , z) ∷ₚ xs ⊙ suc (y + z)) ≡⟨ cong suc (cons-swap y z xs _) ⟩
  suc (xs ⊙ y ↔ z ⊙ suc (y + z)) ≡⟨ cong suc (cong (xs ⊙_) (perm-alg-swap y z _ ; sym (swap-swap′ y _ _ ) ; swap-rhs y _)) ⟩
  suc (xs ⊙ y) ≡˘⟨ cong (bool _ zero) (doesn't (x≢sx+y y z ∘ sym) (suc (y + z) ≟ y)) ⟩
  (if does (suc (y + z) ≟ y) then zero else suc (xs ⊙ y)) ≡⟨⟩
  (zero , suc (y + z)) ∷ xs ⊙ zero ↔ y ⊙ zero ∎
cons-swap₃ zero y z xs (suc n) =
  (zero , suc (y + z)) ∷ (y , z) ∷ₚ xs ⊙ suc n ≡⟨ {!!} ⟩
  (zero , suc (y + z)) ∷ xs ⊙ zero ↔ y ⊙ suc n ∎

cons-swap x y [] z = refl
cons-swap x y ((zₛ , zₜ) ∷ xs) n with cmp-diff x zₛ | cmp-reflects x zₛ
... | just (false , k) | p =
  (x , y) ∷ (k , zₜ) ∷ xs ⊙ n ≡⟨ perm-alg-com x y ((k , zₜ) ∷ xs) n ⟩
  (suc x + k , zₜ) ∷ xs ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → (e , zₜ) ∷ xs ⊙ _) p ⟩
  (zₛ , zₜ) ∷ xs ⊙ (x ↔ y ⊙ n) ∎
... | just (true  , k) | p =
  (zₛ , perm-alg k y id zₜ) ∷ (k , y) ∷ₚ xs ⊙ n ≡⟨ cons-swap₁ zₛ k y zₜ xs n ⟩
  (zₛ , zₜ) ∷ xs ⊙ perm-alg (suc zₛ + k) y id n ≡⟨ cong (λ e → (zₛ , zₜ) ∷ xs ⊙ perm-alg e y id n) p ⟩
  (zₛ , zₜ) ∷ xs ⊙ (x ↔ y ⊙ n) ∎
... | nothing | x≡zₛ with cmp-diff y zₜ | cmp-reflects y zₜ
... | nothing           | y≡zₜ =
  shift (suc x) xs ⊙ n ≡˘⟨ cong (shift (suc x) xs ⊙_) (cong (x ↔_⊙ x ↔ y ⊙ n) (sym y≡zₜ) ; perm-alg-dup x y n) ⟩
  (shift (suc x) xs ⊙ x ↔ zₜ ⊙ x ↔ y ⊙ n) ≡˘⟨ perm-alg-com x zₜ xs (x ↔ y ⊙ n) ⟩
  ((x , zₜ) ∷ xs ⊙ x ↔ y ⊙ n) ≡⟨ cong (λ e → ((e , zₜ) ∷ xs ⊙ x ↔ y ⊙ n)) x≡zₛ  ⟩
  ((zₛ , zₜ) ∷ xs ⊙ x ↔ y ⊙ n) ∎
... | just (false , yz) | yzp =
  (x , zₜ) ∷ (y , yz) ∷ₚ xs ⊙ n ≡⟨ cong (λ e → (x , e) ∷ (y , yz) ∷ₚ xs ⊙ n) (sym yzp) ⟩
  (x , suc (y + yz)) ∷ (y , yz) ∷ₚ xs ⊙ n ≡⟨ cons-swap₃ x y yz xs n ⟩
  (x , suc (y + yz)) ∷ xs ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → (x , e) ∷ xs ⊙ x ↔ y ⊙ n) yzp ⟩
  (x , zₜ) ∷ xs ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → (e , zₜ) ∷ xs ⊙ x ↔ y ⊙ n) x≡zₛ ⟩
  (zₛ , zₜ) ∷ xs ⊙ (x ↔ y ⊙ n) ∎
... | just (true  , yz) | yzp =
  (x , zₜ) ∷ (zₜ , yz) ∷ₚ xs ⊙ n ≡⟨ cons-swap₂ x zₜ xs yz n ⟩
  ((x , zₜ) ∷ xs ⊙ x ↔ suc (zₜ + yz) ⊙ n) ≡⟨ cong₂ (λ e₁ e₂ → (e₁ , zₜ) ∷ xs ⊙ x ↔ e₂ ⊙ n) x≡zₛ yzp ⟩
  (zₛ , zₜ) ∷ xs ⊙ x ↔ y ⊙ n ∎

norm-correct : ∀ xs n → [ xs ]↓ ⊙ n ≡ xs · n
norm-correct [] n = refl
norm-correct ((x , y) ∷ xs) n with cmp-diff x y | cmp-reflects x y 
... | nothing          | p =
  [ xs ]↓ ⊙ n ≡⟨ norm-correct xs n ⟩
  xs · n ≡˘⟨ cong (xs ·_) (swap-id x n) ⟩
  (xs · x ↔ x · n) ≡⟨ cong (λ e → xs · x ↔ e · n) p ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  (x , y) ∷ xs · n ∎
... | just (true  , k) | p = {!!}
... | just (false , k) | p =
  (x , k) ∷ₚ [ xs ]↓ ⊙ n ≡⟨ cons-swap x k [ xs ]↓ n ⟩
  ([ xs ]↓ ⊙ x ↔ k ⊙ n) ≡⟨ cong ([ xs ]↓ ⊙_) (perm-alg-swap x k n) ⟩
  ([ xs ]↓ ⊙ x ↔′ suc x + k · n) ≡˘⟨ cong ([ xs ]↓ ⊙_) (swap-swap′ x _ n) ⟩
  ([ xs ]↓ ⊙ x ↔  suc x + k · n) ≡⟨ cong (λ e → [ xs ]↓ ⊙ x ↔ e · n) p ⟩
  ([ xs ]↓ ⊙ x ↔ y · n) ≡⟨ norm-correct xs (x ↔ y · n) ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  (x , y) ∷ xs · n ∎
