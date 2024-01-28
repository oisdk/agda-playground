{-# OPTIONS --allow-unsolved-metas #-}

module Data.Permutation where

open import Prelude
open import Data.List
open import Data.Nat.Properties renaming (discreteℕ to _≟_)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Data.List.Properties

--------------------------------------------------------------------------------
-- Unnormalised Representation
--------------------------------------------------------------------------------

Swaps : Type
Swaps = List (ℕ × ℕ)

swap : ℕ → ℕ → ℕ → ℕ
swap x y z =
  if does (x ≟ z) then y else
  if does (y ≟ z) then x else
  z

swap-lhs : ∀ x y → swap x y x ≡ y
swap-lhs x y with does (x ≟ x) | why (x ≟ x)
... | true  | _ = refl
... | false | x≢x = ⊥-elim (x≢x refl)

swap-rhs : ∀ x y → swap x y y ≡ x
swap-rhs x y with does (x ≟ y) | why (x ≟ y)
... | true  | x≡y = sym x≡y
... | false | _ with does (y ≟ y) | why (y ≟ y)
... | false | y≢y = ⊥-elim (y≢y refl)
... | true  | _ = refl

swap-id : ∀ x y → swap x x y ≡ y
swap-id x y with does (x ≟ y) | why (x ≟ y)
... | false | _ = refl
... | true  | x≡y = x≡y

_·_ : Swaps → ℕ → ℕ
_·_ = flip (foldl (flip (uncurry swap)))

--------------------------------------------------------------------------------
-- Normalised Representation
--------------------------------------------------------------------------------

Diffs : Type
Diffs = List (ℕ × ℕ)

unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
unflatten-alg x y k n = ((n + x) , suc (n + x + y)) ∷ k (suc n + x)

unflatten : Diffs → Swaps
unflatten xs = foldr (uncurry unflatten-alg) (const []) xs 0

swap′ : ℕ → ℕ → ℕ → ℕ
swap′ zero zero z = z
swap′ zero y@(suc _) zero = y
swap′ zero (suc y) (suc z) = if does (y ≟ z) then zero else suc z
swap′ x@(suc _) zero zero = x
swap′ (suc x) (suc y) zero = zero
swap′ (suc x) zero (suc z) = if does (x ≟ z) then zero else suc z
swap′ (suc x) (suc y) (suc z) = suc (swap′ x y z)

swap-suc : ∀ x y z → swap (suc x) (suc y) (suc z) ≡ suc (swap x y z)
swap-suc x y z with does (x ≟ z)
... | true = refl
... | false with does (y ≟ z)
... | false = refl
... | true = refl

swap-swap′ : ∀ x y z → swap x y z ≡ swap′ x y z
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

_⊙_ : Diffs → ℕ → ℕ
_⊙_ = foldr (uncurry perm-alg) id

perm-alg-swap : ∀ x y z → perm-alg x y id z ≡ swap′ x (suc (x + y)) z
perm-alg-swap zero y zero = refl
perm-alg-swap zero y (suc z) = refl
perm-alg-swap (suc x) y zero = refl
perm-alg-swap (suc x) y (suc z) = cong suc (perm-alg-swap x y z)

shift : ℕ → Diffs → Diffs
shift m [] = []
shift m ((x , y) ∷ xs) = (m + x , y) ∷ xs

perm-alg-com : ∀ x y xs z → ((x , y) ∷ xs) ⊙ z ≡ shift (suc x) xs ⊙ perm-alg x y id z
perm-alg-com x y [] z = refl
perm-alg-com zero y (w ∷ xs) zero = refl
perm-alg-com (suc x) y (w ∷ xs) zero = refl
perm-alg-com (suc x) y (w ∷ xs) (suc z) = cong suc (perm-alg-com x y (w ∷ xs) z)
perm-alg-com zero y (w ∷ xs) (suc z) with does (y ≟ z)
... | false = refl
... | true  = refl

swap-unf-alg : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
swap-unf-alg x y k m n = k (suc m + x) (swap (m + x) (suc (m + x + y)) n)

swap-unf′ : Swaps → ℕ → ℕ → ℕ
swap-unf′ = foldr (uncurry swap-unf-alg) (const id)

swap-shift : ∀ m n xs → shift m xs ⊙ n ≡ swap-unf′ xs m n
swap-shift m n [] = refl
swap-shift m n ((x , y) ∷ xs) =
  perm-alg (m + x) y (_⊙_ xs) n
    ≡⟨ perm-alg-com (m + x) y xs n ⟩
  shift (suc m + x) xs ⊙ perm-alg (m + x) y id n
    ≡⟨ cong (_⊙_ (shift (suc m + x) xs)) (perm-alg-swap (m + x) y n) ⟩
  shift (suc m + x) xs ⊙ swap′ (m + x) (suc (m + x + y)) n
    ≡˘⟨ cong (_⊙_ (shift (suc m + x) xs)) (swap-swap′ (m + x) _ n) ⟩
  shift (suc m + x) xs ⊙ swap (m + x) (suc (m + x + y)) n
    ≡⟨ swap-shift (suc m + x) _ xs ⟩
  swap-unf′ xs (suc m + x) (swap (m + x) (suc (m + x + y)) n)
    ≡⟨⟩
  swap-unf-alg x y (swap-unf′ xs) m n ∎

shift-0 : ∀ xs → shift 0 xs ≡ xs
shift-0 [] = refl
shift-0 (x ∷ xs) = refl

swaps-compress : ∀ xs n → xs ⊙ n ≡ unflatten xs · n
swaps-compress xs n =
  xs ⊙ n
    ≡˘⟨ cong (_⊙ n) (shift-0 xs) ⟩
  shift 0 xs ⊙ n
    ≡⟨ swap-shift 0 n xs ⟩
  swap-unf′ xs 0 n
    ≡˘⟨ cong′ {A = ℕ → ℕ → ℕ} (λ e → e 0 n) (foldr-fusion (λ xs m n → foldl-by-r (flip (uncurry swap)) n (xs m)) (const []) (λ _ _ → refl) xs) ⟩
  foldl-by-r (flip (uncurry swap)) n (unflatten xs)
    ≡˘⟨ foldl-is-foldr (flip (uncurry swap)) n (unflatten xs) ⟩
  unflatten xs · n ∎
  
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

cons : ℕ × ℕ → Diffs → Diffs
cons x [] = x ∷ []
cons (xₛ , xₜ) ((yₛ , yₜ) ∷ xs) = case cmp-diff xₛ yₛ of
  λ { nothing → maybe (shift (suc xₛ) xs) (λ lg → (xₛ , yₜ) ∷ cons lg xs) (swap-diff xₜ yₜ)
    ; (just (false , yₛ)) → (xₛ , xₜ) ∷ (yₛ , yₜ) ∷ xs
    ; (just (true  , xₛ)) → (yₛ , perm-alg xₛ xₜ id yₜ) ∷ cons (xₛ , xₜ) xs
    }

norm : Swaps → Diffs
norm = foldr cons [] ∘ catMaybes (uncurry swap-diff)

cons-swap : ∀ x y xs z → cons (x , y) xs ⊙ z ≡ xs ⊙ swap′ x (suc x + y) z
cons-swap x y [] z = perm-alg-swap x y z
cons-swap x y ((zₛ , zₜ) ∷ xs) n with cmp-diff x zₛ | cmp-reflects x zₛ
... | nothing          | p = {!!}
... | just (false , k) | p =
  ((x , y) ∷ (k , zₜ) ∷ xs) ⊙ n ≡⟨ perm-alg-com x y ((k , zₜ) ∷ xs) n ⟩
  ((suc x + k , zₜ) ∷ xs) ⊙ perm-alg x y id n ≡⟨ cong₂ _⊙_ (cong (λ e → ((e , zₜ) ∷ xs)) p) (perm-alg-swap x y n) ⟩
  ((zₛ , zₜ) ∷ xs) ⊙ swap′ x (suc (x + y)) n ∎
... | just (true  , k) | p = {!!}

norm-correct : ∀ xs n → norm xs ⊙ n ≡ xs · n
norm-correct [] n = refl
norm-correct ((x , y) ∷ xs) n with cmp-diff x y | cmp-reflects x y 
... | nothing          | p =
  _⊙_ (norm xs) n ≡⟨ norm-correct xs n ⟩
  _·_ xs n ≡˘⟨ cong (xs ·_) (swap-id x n) ⟩
  _·_ xs (swap x x n) ≡⟨ cong (λ e → xs · swap x e n) p ⟩
  _·_ xs (swap x y n) ≡⟨⟩
  _·_ ((x , y) ∷ xs) n ∎
... | just (true  , k) | p = {!!}
... | just (false , k) | p =
  cons (x , k) (norm xs) ⊙ n ≡⟨ cons-swap x k (norm xs) n ⟩
  norm xs ⊙ swap′ x (suc x + k) n ≡˘⟨ cong (norm xs ⊙_) (swap-swap′ x _ n) ⟩
  norm xs ⊙ swap x (suc x + k) n ≡⟨ cong (λ e → norm xs ⊙ swap x e n) p ⟩
  norm xs ⊙ swap x y n ≡⟨ norm-correct xs (swap x y n) ⟩
  xs · swap x y n ≡⟨⟩
  ((x , y) ∷ xs) · n ∎
