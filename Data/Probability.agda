{-# OPTIONS --cubical --safe #-}

module Data.Probability where

open import Prelude
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Bits renaming (Bits to ℚ⁺; [] to 1ℚ; 0∷_ to lℚ; 1∷_ to rℚ)
open import Data.Bits.Equatable

open import Data.Bits.Fold

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

data ℙ : Type where
  ℙ⁰ : ℙ
  ℙ¹ : ℙ
  ℙ∙ : ℚ⁺ → ℙ

unEu : ℚ⁺ → ℙ
unEu 1ℚ = ℙ¹
unEu (lℚ x) = ℙ∙ x
unEu (rℚ x) = ℙ¹ -- won't happen

_/suc_ : ℕ → ℕ → ℙ
zero  /suc d = ℙ⁰
suc n /suc d = unEu (normalise-suc n d)

_/_ : ℕ → ℕ → ℙ
n / zero = ℙ⁰
n / suc d = n /suc d


zer : (ℕ × ℕ) → (ℕ × ℕ)
zer (p , q) = p , suc p ℕ.+ q

one : (ℕ × ℕ) → (ℕ × ℕ)
one (p , q) = suc p ℕ.+ q , q

norm : (ℕ × ℕ) → ℕ × ℕ
norm (x , y) = suc x , suc y

prob : ℙ → (ℕ × ℕ)
prob ℙ⁰ = 0 , 1
prob ℙ¹ = 1 , 1
prob (ℙ∙ x) = norm (zer (foldr-bits zer one (0 , 0) x))

mul″ : ℙ → ℙ → ℙ
mul″ x y =
  let xn , xd = prob x
      yn , yd = prob y
  in (xn ℕ.* yn) / (xd ℕ.* yd)

-- e = prob (5 /suc 22)

nextFrac : ℚ⁺ → ℚ⁺
nextFrac 1ℚ = lℚ 1ℚ
nextFrac (lℚ x) = rℚ x
nextFrac (rℚ x) = lℚ (nextFrac x)

open import Data.List

fracs : ℕ → List ℙ
fracs n = ℙ⁰ ∷ ℙ¹ ∷ go n 1ℚ
  where
  go : ℕ → ℚ⁺ → List ℙ
  go zero    x = []
  go (suc n) x = ℙ∙ x ∷ go n (nextFrac x)

open import Data.List.Sugar using (liftA2)

-- mul′ : ℚ⁺ → ℚ⁺ → ℚ⁺
-- mul′ 1ℚ 1ℚ = lℚ (lℚ 1ℚ)
-- mul′ 1ℚ (lℚ ys) = {!!}
-- mul′ 1ℚ (rℚ ys) = {!!}
-- mul′ (lℚ xs) 1ℚ = {!!}
-- mul′ (lℚ xs) (lℚ ys) = {!!}
-- mul′ (lℚ xs) (rℚ ys) = {!!}
-- mul′ (rℚ xs) 1ℚ = {!!}
-- mul′ (rℚ xs) (lℚ ys) = {!!}
-- mul′ (rℚ xs) (rℚ ys) = {!!}

-- mul : ℙ → ℙ → ℙ
-- mul ℙ⁰ ys = ℙ⁰
-- mul ℙ¹ ys = ys
-- mul (ℙ∙ x) ℙ⁰ = ℙ⁰
-- mul xs ℙ¹ = xs
-- mul (ℙ∙ x) (ℙ∙ y) = ℙ∙ (mul′ x y)


-- testMul : ℕ → Type
-- testMul n = liftA2 mul xs xs ≡ liftA2 mul″ xs xs
--   where
--     xs : List ℙ
--     xs = fracs n

-- _ : testMul 5
-- _ = refl
