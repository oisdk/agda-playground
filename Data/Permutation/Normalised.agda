module Data.Permutation.Normalised where

open import Prelude hiding (_↔_)
open import Data.Nat.Properties renaming (discreteℕ to infix 4 _≟_)
open import Data.Nat using (_+_)
open import Path.Reasoning
open import Data.List.Properties
open import Data.List hiding ([]; _∷_)
open import Data.Permutation.Swap _≟_
open import Data.Permutation.NonNorm _≟_

--------------------------------------------------------------------------------
-- Diffs type
--------------------------------------------------------------------------------

Diffs : Type
Diffs = List (ℕ × ℕ)

--------------------------------------------------------------------------------
-- Applying a normalised permutation
--------------------------------------------------------------------------------

⊙-alg : ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ
⊙-alg zero    y k zero    = suc (k y)
⊙-alg zero    y k (suc z) = if does (y ≟ z) then zero else suc (k z)
⊙-alg (suc x) y k zero    = zero
⊙-alg (suc x) y k (suc z) = suc (⊙-alg x y k z)

infixr 4.5 _⊙_
_⊙_ : Diffs → ℕ → ℕ
_⊙_ = foldr (uncurry ⊙-alg) id

infixr 4.5 _↔_⊙_
_↔_⊙_ : ℕ → ℕ → ℕ → ℕ
_↔_⊙_ x y = ⊙-alg x y id

--------------------------------------------------------------------------------
-- Unnormalise a permutation
--------------------------------------------------------------------------------

unflatten-alg : ℕ → ℕ → (ℕ → Swaps) → ℕ → Swaps
unflatten-alg x y k n = k (suc n + x) ∘⟨ n + x , suc (n + x + y) ⟩

[_]↑ : Diffs → Swaps
[ xs ]↑ = foldr (uncurry unflatten-alg) (const ⟨⟩) xs 0

--------------------------------------------------------------------------------
-- Support of a permutation
--------------------------------------------------------------------------------

supp : Diffs → List ℕ
supp = foldr (λ { (x , y) xs → map (suc x +_) (xs ∘⟨ y ⟩) ∘⟨ x ⟩ }) ⟨⟩

--------------------------------------------------------------------------------
-- Unnormalise Proof
--------------------------------------------------------------------------------

swap-suc : ∀ x y z → suc x ↔ suc y · suc z ≡ suc (x ↔ y · z)
swap-suc x y z with does (x ≟ z)
... | true = refl
... | false with does (y ≟ z)
... | false = refl
... | true = refl

⊙-· : ∀ x y z → x ↔ y ⊙ z ≡ x ↔ suc x + y · z
⊙-· (suc x) y (suc z) = cong suc (⊙-· x y z) ; sym (swap-suc x (suc (x + y)) z)
⊙-· (suc x) y zero    = refl
⊙-· zero    y zero    = refl
⊙-· zero    y (suc z) = refl

infixl 5 _⊙+_
_⊙+_ : Diffs → ℕ → Diffs
⟨⟩ ⊙+ _ = ⟨⟩
xs ∘⟨ x , y ⟩ ⊙+ m = xs ∘⟨ m + x , y ⟩

⊙-alg-com : ∀ x y xs z → xs ∘⟨ x , y ⟩ ⊙ z ≡ xs ⊙+ suc x ⊙ x ↔ y ⊙ z
⊙-alg-com x y ⟨⟩ z = refl
⊙-alg-com zero y (xs ∘⟨ w ⟩) zero = refl
⊙-alg-com (suc x) y (xs ∘⟨ w ⟩) zero = refl
⊙-alg-com (suc x) y (xs ∘⟨ w ⟩) (suc z) = cong suc (⊙-alg-com x y (xs ∘⟨ w ⟩) z)
⊙-alg-com zero y (xs ∘⟨ w ⟩) (suc z) with does (y ≟ z)
... | false = refl
... | true  = refl

swap-unf-alg : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
swap-unf-alg x y k m n = k (suc m + x) (m + x ↔ suc (m + x + y) · n)

swap-shift : ∀ m n xs → xs ⊙+ m ⊙ n ≡ foldr (uncurry swap-unf-alg) (const id) xs m n
swap-shift m n ⟨⟩ = refl
swap-shift m n (xs ∘⟨ x , y ⟩) =
  ⊙-alg (m + x) y (xs ⊙_) n
    ≡⟨ ⊙-alg-com (m + x) y xs n ⟩
  (xs ⊙+ suc m + x ⊙ m + x ↔ y ⊙ n)
    ≡⟨ cong (xs ⊙+ suc m + x ⊙_) (⊙-· (m + x) y n) ⟩
  xs ⊙+ suc m + x ⊙ m + x ↔ suc m + x + y · n
    ≡⟨ swap-shift (suc m + x) _ xs ⟩
  swap-unf-alg x y (foldr (uncurry swap-unf-alg) (const id) xs) m n ∎

shift-0 : ∀ xs → xs ⊙+ 0 ≡ xs
shift-0 ⟨⟩ = refl
shift-0 (xs ∘⟨ w ⟩) = refl

swaps-compress : ∀ xs n → xs ⊙ n ≡ [ xs ]↑ · n
swaps-compress xs n =
  xs ⊙ n
    ≡˘⟨ cong (_⊙ n) (shift-0 xs) ⟩
  xs ⊙+ 0 ⊙ n
    ≡⟨ swap-shift 0 n xs ⟩
  foldr (uncurry swap-unf-alg) (const id) xs 0 n
    ≡˘⟨ cong′ {A = ℕ → ℕ → ℕ} (λ e → e 0 n) (foldr-fusion (λ xs m n → foldl-by-r (flip (uncurry _↔_·_)) n (xs m)) (const ⟨⟩) (λ _ _ → refl) xs) ⟩
  foldl-by-r (flip (uncurry _↔_·_)) n [ xs ]↑
    ≡˘⟨ foldl-is-foldr (flip (uncurry _↔_·_)) n [ xs ]↑ ⟩
  [ xs ]↑ · n ∎
  
--------------------------------------------------------------------------------
-- Find range of permutatiuon 
--------------------------------------------------------------------------------

max-num-alg : ℕ × ℕ → ℕ → ℕ
max-num-alg (x , y) z = suc (x + (y ⊔ z))

max-num : Diffs → ℕ
max-num = foldr max-num-alg zero

disp-diffs : Diffs → List ℕ
disp-diffs d = map (d ⊙_) (0 ⋯ max-num d)

max-swaps : Swaps → ℕ
max-swaps = foldr (λ { (x , y) z → x ⊔ y ⊔ z }) zero

disp-swaps : Swaps → List ℕ
disp-swaps d = map (d ·_) (0 ⋯ max-swaps d)

--------------------------------------------------------------------------------
-- Normalise a permutation
--------------------------------------------------------------------------------

open import Data.Maybe using (mapMaybe)
open import Data.Nat.Compare

swap-diff : ℕ → ℕ → Maybe (ℕ × ℕ)
swap-diff x y = mapMaybe (map₁ (bool′ x y)) (compare x y)

infixl 5 _⊙⟨_⟩
_⊙⟨_⟩ : Diffs → ℕ × ℕ → Diffs
⟨⟩ ⊙⟨ p ⟩ = ⟨⟩ ∘⟨ p ⟩
xs ∘⟨ yₛ , yₜ ⟩ ⊙⟨ xₛ , xₜ ⟩ = case compare xₛ yₛ of
  λ { equal           → maybe (xs ⊙+ suc xₛ) (λ lg → xs ⊙⟨ lg ⟩ ∘⟨ xₛ , yₜ ⟩) (swap-diff xₜ yₜ)
    ; (less    yₛ-xₛ-1) → xs ∘⟨ yₛ-xₛ-1 , yₜ ⟩ ∘⟨ xₛ , xₜ ⟩
    ; (greater xₛ-yₛ-1) → xs ⊙⟨ xₛ-yₛ-1 , xₜ ⟩ ∘⟨ yₛ , xₛ-yₛ-1 ↔ xₜ ⊙ yₜ ⟩
    }

[_]↓ : Swaps → Diffs
[_]↓ = foldr (flip _⊙⟨_⟩) ⟨⟩ ∘ catMaybes (uncurry swap-diff)

--------------------------------------------------------------------------------
-- Normalisation proof
--------------------------------------------------------------------------------

⊙-alg-dup : ∀ x y z → x ↔ y ⊙ x ↔ y ⊙ z ≡ z
⊙-alg-dup zero y zero = cong (bool′ _ _) (it-does (y ≟ y) refl)
⊙-alg-dup (suc x) y zero = refl
⊙-alg-dup (suc x) y (suc z) = cong suc (⊙-alg-dup x y z)
⊙-alg-dup zero y (suc z) with does (y ≟ z) | why (y ≟ z)
... | true  | y≡z = cong suc y≡z
... | false | y≢z = cong (bool′ _ _) (it-doesn't (y ≟ z) y≢z)

⊙-cong : ∀ w x y z → does (w ↔ x ⊙ y ≟ z) ≡ does (y ≟ w ↔ x ⊙ z)
⊙-cong w x y z =
  both-do
    (w ↔ x ⊙ y ≟ z)
    (y ≟ w ↔ x ⊙ z)
    ((sym (⊙-alg-dup w x y) ;_ ∘′ cong (w ↔ x ⊙_)) iff (_; ⊙-alg-dup w x z ∘′ cong (w ↔ x ⊙_) ))


cons-swap : ∀ x y xs z → xs ⊙⟨ x , y ⟩ ⊙ z ≡ xs ⊙ x ↔ y ⊙ z
cons-swap₁ : ∀ x k y z xs n → xs ⊙⟨ k , y ⟩ ∘⟨ x , k ↔ y ⊙ z ⟩ ⊙ n ≡ xs ∘⟨ x , z ⟩ ⊙ suc x + k ↔ y ⊙ n

cons-swap₁ (suc x) k y z xs (suc n) = cong suc (cons-swap₁ x k y z xs n)
cons-swap₁ (suc x) k y z xs zero = refl
cons-swap₁ zero k y z xs zero = cong suc (cons-swap k y xs (k ↔ y ⊙ z) ; cong (xs ⊙_) (⊙-alg-dup k y z))
cons-swap₁ zero k y z xs (suc n) = 
  xs ⊙⟨ k , y ⟩ ∘⟨ zero , k ↔ y ⊙ z ⟩ ⊙ suc n ≡⟨⟩
  (if does (k ↔ y ⊙ z ≟ n) then zero else suc (xs ⊙⟨ k , y ⟩ ⊙ n)) ≡⟨ cong (λ e → if does (k ↔ y ⊙ z ≟ n) then zero else suc e) (cons-swap k y xs n) ⟩
  (if does (k ↔ y ⊙ z ≟ n) then zero else suc (xs ⊙ k ↔ y ⊙ n)) ≡⟨ cong (bool′ (suc (xs ⊙ k ↔ y ⊙ n)) zero) (⊙-cong k y z n) ⟩
  (if does (z ≟ k ↔ y ⊙ n) then zero else suc (xs ⊙ k ↔ y ⊙ n)) ≡⟨⟩
  xs ∘⟨ zero , z ⟩ ⊙ suc (k ↔ y ⊙ n) ≡⟨⟩
  xs ∘⟨ zero , z ⟩ ⊙ suc k ↔ y ⊙ suc n ∎

cons-swap₂ : ∀ x y xs z n → xs ⊙⟨ y , z ⟩ ∘⟨ x , y ⟩ ⊙ n ≡ xs ∘⟨ x , y ⟩ ⊙ x ↔ suc y + z ⊙ n
cons-swap₂ (suc x) y xs z zero = refl
cons-swap₂ (suc x) y xs z (suc n) = cong suc (cons-swap₂ x y xs z n)
cons-swap₂ zero y xs z zero with does (y ≟ suc y + z) | why (y ≟ suc y + z)
... | false | p = cong suc $
  xs ⊙⟨ y , z ⟩ ⊙ y ≡⟨ cons-swap y z xs y ⟩
  xs ⊙ (y ↔ z ⊙ y) ≡⟨ cong (xs ⊙_) (⊙-· y z y ; swap-lhs y (suc y + z) ) ⟩
  xs ⊙ suc y + z ∎
... | true  | p = ⊥-elim (x≢sx+y y z p)
cons-swap₂ zero y xs z (suc n) with does (y ≟ n) | why (y ≟ n) | does (suc y + z ≟ n) | why (suc y + z ≟ n)
cons-swap₂ zero y xs z (suc n) | true | ynp | true | synp = ⊥-elim (x≢sx+y n z (sym synp ; cong suc (cong (_+ z) ynp)))
cons-swap₂ zero y xs z (suc n) | false | ynp | true | synp = cong suc (cons-swap y z xs n ; cong (xs ⊙_) (⊙-· y z n ; cong (y ↔_· n) synp ; swap-rhs y n))
cons-swap₂ zero y xs z (suc n) | yn | ynp | false | synp with does (y ≟ n) | why (y ≟ n)
cons-swap₂ zero y xs z (suc n) | false | ynp | false | synp | true | ynp′ = ⊥-elim (ynp ynp′)
cons-swap₂ zero y xs z (suc n) | true | ynp | false | synp | false | ynp′ = ⊥-elim (ynp′ ynp)
cons-swap₂ zero y xs z (suc n) | true | ynp | false | synp | true | ynp′ = refl
cons-swap₂ zero y xs z (suc n) | false | ynp | false | synp | false | ynp′ = cong suc (cons-swap y z xs n ; cong (xs ⊙_) (⊙-· y z n ; swap-neq y _ n ynp synp))

cons-swap₃ : ∀ x y z xs n → xs ⊙⟨ y , z ⟩ ∘⟨ x , suc y + z ⟩ ⊙ n ≡ xs ∘⟨ x , suc y + z ⟩ ⊙ x ↔ y ⊙ n
cons-swap₃ (suc x) y z xs zero = refl
cons-swap₃ (suc x) y z xs (suc n) = cong suc (cons-swap₃ x y z xs n)
cons-swap₃ zero y z xs zero =
  suc (xs ⊙⟨ y , z ⟩ ⊙ suc y + z) ≡⟨ cong suc (cons-swap y z xs _) ⟩
  suc (xs ⊙ y ↔ z ⊙ suc y + z) ≡⟨ cong suc (cong (xs ⊙_) (⊙-· y z _ ; swap-rhs y _)) ⟩
  suc (xs ⊙ y) ≡˘⟨ cong (bool _ zero) (it-doesn't  (suc y + z ≟ y) (x≢sx+y y z ∘ sym)) ⟩
  xs ∘⟨ zero , suc y + z ⟩ ⊙ zero ↔ y ⊙ zero ∎
cons-swap₃ zero y z xs (suc n) with does (y ≟ n) | why (y ≟ n)
... | true | y≡n =
  (xs ⊙⟨ y , z ⟩ ∘⟨ zero , suc y + z ⟩ ⊙ suc n) ≡⟨ cong (bool′ _ _) (it-doesn't (suc y + z ≟ n) (x≢sx+y y z ∘ sym ∘ _; sym y≡n)) ⟩
  suc (xs ⊙⟨ y , z ⟩ ⊙ n) ≡⟨ cong suc (cons-swap y z xs n) ⟩
  suc (xs ⊙ y ↔ z ⊙ n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (⊙-· y z n) ⟩
  suc (xs ⊙ y ↔ suc y + z · n) ≡⟨ cong (λ e → suc (xs ⊙ e ↔ suc y + z · n)) y≡n ⟩
  suc (xs ⊙ n ↔ suc y + z · n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (swap-lhs n _)  ⟩
  suc (xs ⊙ suc y + z) ∎
... | false | y≢n with does (suc y + z ≟ n) | why (suc y + z ≟ n)
... | true | _ = refl
... | false | sy+z≢n =
  suc (xs ⊙⟨ y , z ⟩ ⊙ n) ≡⟨ cong suc (cons-swap y z xs n) ⟩
  suc (xs ⊙ y ↔ z ⊙ n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (⊙-· y z n) ⟩
  suc (xs ⊙ y ↔ suc y + z · n) ≡⟨ cong (λ e → suc (xs ⊙ e)) (swap-neq y _ n y≢n sy+z≢n) ⟩
  suc (xs ⊙ n) ∎

-- ⊙-alg-com : ∀ x y xs z → xs ∘⟨ x , y ⟩ ⊙ z ≡ xs ⊙+ suc x ⊙ x ↔ y ⊙ z
-- ⊙-· : ∀ x y z → x ↔ y ⊙ z ≡ x ↔ suc x + y · z
-- cons-swap₁ : ∀ x k y z xs n → xs ⊙⟨ k , y ⟩ ∘⟨ x , k ↔ y ⊙ z ⟩ ⊙ n ≡ xs ∘⟨ x , z         ⟩ ⊙ suc x + k ↔ y         ⊙ n
-- cons-swap₂ : ∀ x y xs z   n → xs ⊙⟨ y , z ⟩ ∘⟨ x , y         ⟩ ⊙ n ≡ xs ∘⟨ x , y         ⟩ ⊙ x         ↔ suc y + z ⊙ n
-- cons-swap₃ : ∀ x y z xs   n → xs ⊙⟨ y , z ⟩ ∘⟨ x , suc y + z ⟩ ⊙ n ≡ xs ∘⟨ x , suc y + z ⟩ ⊙ x         ↔ y         ⊙ n

cons-swap x y ⟨⟩ z = refl
cons-swap x y (xs ∘⟨ zₛ , zₜ ⟩) n with compare x zₛ | comparing x zₛ
... | less k | p =
  xs ∘⟨ k , zₜ ⟩ ∘⟨ x , y ⟩ ⊙ n ≡⟨ ⊙-alg-com x y (xs ∘⟨ k , zₜ ⟩) n ⟩
  xs ∘⟨ suc x + k , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ e , zₜ ⟩ ⊙ _) p ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ∎
... | greater k | p =
  xs ⊙⟨ k , y ⟩ ∘⟨ zₛ , k ↔ y ⊙ zₜ ⟩ ⊙ n ≡⟨ cons-swap₁ zₛ k y zₜ xs n ⟩
  (xs ∘⟨ zₛ , zₜ ⟩ ⊙ suc zₛ + k ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ zₛ , zₜ ⟩ ⊙ e ↔ y ⊙ n) p ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ x ↔ y ⊙ n ∎
... | equal | x≡zₛ with compare y zₜ | comparing y zₜ
... | equal | y≡zₜ =
  xs ⊙+ suc x ⊙ n ≡˘⟨ cong (xs ⊙+ suc x ⊙_) (cong (x ↔_⊙ x ↔ y ⊙ n) (sym y≡zₜ) ; ⊙-alg-dup x y n) ⟩
  (xs ⊙+ suc x ⊙ x ↔ zₜ ⊙ x ↔ y ⊙ n) ≡˘⟨ ⊙-alg-com x zₜ xs (x ↔ y ⊙ n) ⟩
  (xs ∘⟨ x , zₜ ⟩ ⊙ x ↔ y ⊙ n) ≡⟨ cong (λ e → (xs ∘⟨ e , zₜ ⟩ ⊙ x ↔ y ⊙ n)) x≡zₛ  ⟩
  (xs ∘⟨ zₛ , zₜ ⟩ ⊙ x ↔ y ⊙ n) ∎
... | less zₜ-y-1 | yzp =
  xs ⊙⟨ y , zₜ-y-1 ⟩ ∘⟨ x , zₜ ⟩ ⊙ n ≡⟨ cong (λ e → xs ⊙⟨ y , zₜ-y-1 ⟩ ∘⟨ x , e ⟩ ⊙ n) (sym yzp) ⟩
  xs ⊙⟨ y , zₜ-y-1 ⟩ ∘⟨ x , suc y + zₜ-y-1 ⟩ ⊙ n ≡⟨ cons-swap₃ x y zₜ-y-1 xs n ⟩
  xs ∘⟨ x , suc y + zₜ-y-1 ⟩ ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ x , e ⟩ ⊙ x ↔ y ⊙ n) yzp ⟩
  xs ∘⟨ x  , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ≡⟨ cong (λ e → xs ∘⟨ e , zₜ ⟩ ⊙ x ↔ y ⊙ n) x≡zₛ ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ (x ↔ y ⊙ n) ∎
... | greater yz | yzp =
  xs ⊙⟨ zₜ , yz ⟩ ∘⟨ x , zₜ ⟩ ⊙ n ≡⟨ cons-swap₂ x zₜ xs yz n ⟩
  (xs ∘⟨ x , zₜ ⟩ ⊙ x ↔ suc (zₜ + yz) ⊙ n) ≡⟨ cong₂ (λ e₁ e₂ → xs ∘⟨ e₁ , zₜ ⟩ ⊙ x ↔ e₂ ⊙ n) x≡zₛ yzp ⟩
  xs ∘⟨ zₛ , zₜ ⟩ ⊙ x ↔ y ⊙ n ∎

norm-correct : ∀ xs n → [ xs ]↓ ⊙ n ≡ xs · n
norm-correct ⟨⟩ n = refl
norm-correct (xs ∘⟨ x , y ⟩) n with compare x y | comparing x y 
... | equal | p =
  [ xs ]↓ ⊙ n ≡⟨ norm-correct xs n ⟩
  xs · n ≡˘⟨ cong (xs ·_) (swap-id x n) ⟩
  (xs · x ↔ x · n) ≡⟨ cong (λ e → xs · x ↔ e · n) p ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
... | less k | p =
  [ xs ]↓ ⊙⟨ x , k ⟩ ⊙ n ≡⟨ cons-swap x k [ xs ]↓ n ⟩
  ([ xs ]↓ ⊙ x ↔ k ⊙ n) ≡⟨ cong ([ xs ]↓ ⊙_) (⊙-· x k n) ⟩
  ([ xs ]↓ ⊙ x ↔ suc x + k · n) ≡⟨ cong (λ e → [ xs ]↓ ⊙ x ↔ e · n) p ⟩
  ([ xs ]↓ ⊙ x ↔ y · n) ≡⟨ norm-correct xs (x ↔ y · n) ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
... | greater k | p =
  [ xs ]↓ ⊙⟨ y , k ⟩ ⊙ n ≡⟨ cons-swap y k [ xs ]↓ n ⟩
  ([ xs ]↓ ⊙ y ↔ k ⊙ n) ≡⟨ cong ([ xs ]↓ ⊙_) (⊙-· y k n) ⟩
  ([ xs ]↓ ⊙ y ↔ suc y + k · n) ≡⟨ cong (λ e → [ xs ]↓ ⊙ y ↔ e · n) p ⟩
  ([ xs ]↓ ⊙ y ↔ x · n) ≡⟨ norm-correct xs (y ↔ x · n) ⟩
  (xs · y ↔ x · n) ≡⟨ cong (xs ·_) (swap-com y x n) ⟩
  (xs · x ↔ y · n) ≡⟨⟩
  xs ∘⟨ x , y ⟩ · n ∎
