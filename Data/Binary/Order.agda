{-# OPTIONS --cubical --safe #-}

module Data.Binary.Order where

open import Prelude
open import Data.Binary.Definition

infix 4 _≲ᴮ_&_
_≲ᴮ_&_ : 𝔹 → 𝔹 → Bool → Bool
0ᵇ    ≲ᴮ ys    & true  = true
0ᵇ    ≲ᴮ 0ᵇ    & false = false
0ᵇ    ≲ᴮ 1ᵇ ys & false = true
0ᵇ    ≲ᴮ 2ᵇ ys & false = true
1ᵇ xs ≲ᴮ 0ᵇ    & s     = false
1ᵇ xs ≲ᴮ 1ᵇ ys & s     = xs ≲ᴮ ys & s
1ᵇ xs ≲ᴮ 2ᵇ ys & s     = xs ≲ᴮ ys & true
2ᵇ xs ≲ᴮ 0ᵇ    & s     = false
2ᵇ xs ≲ᴮ 1ᵇ ys & s     = xs ≲ᴮ ys & false
2ᵇ xs ≲ᴮ 2ᵇ ys & s     = xs ≲ᴮ ys & s

infix 4 _≤ᴮ_ _<ᴮ_
_≤ᴮ_ : 𝔹 → 𝔹 → Bool
xs ≤ᴮ ys = xs ≲ᴮ ys & true

_<ᴮ_ : 𝔹 → 𝔹 → Bool
xs <ᴮ ys = xs ≲ᴮ ys & false

infix 4 _≤_ _<_
_≤_ : 𝔹 → 𝔹 → Type₀
xs ≤ ys = T (xs ≤ᴮ ys)

_<_ : 𝔹 → 𝔹 → Type₀
xs < ys = T (xs <ᴮ ys)

-- weaken : ∀ xs ys → T (xs ≲ᴮ ys & false) → T (xs ≲ᴮ ys & true)
-- weaken 0ᵇ ys xs≲ys = tt
-- weaken (1ᵇ x) 0ᵇ xs≲ys = xs≲ys
-- weaken (1ᵇ x) (1ᵇ x₁) xs≲ys = weaken x x₁ xs≲ys
-- weaken (1ᵇ x) (2ᵇ x₁) xs≲ys = xs≲ys
-- weaken (2ᵇ x) 0ᵇ xs≲ys = xs≲ys
-- weaken (2ᵇ x) (1ᵇ x₁) xs≲ys = xs≲ys
-- weaken (2ᵇ x) (2ᵇ x₁) xs≲ys = weaken x x₁ xs≲ys

-- ≲-trans : ∀ sₒ xs ys zs s₁ s₂ → T (xs ≲ᴮ ys & s₁) → T (ys ≲ᴮ zs & s₂) → T (xs ≲ᴮ zs & (sₒ or s₁ and s₂))
-- ≲-trans true 0ᵇ       ys zs s₁ s₂ xs≲ys ys≲zs = tt
-- ≲-trans true (1ᵇ xs) (1ᵇ ys) (1ᵇ zs) s₁    s₂ xs≲ys ys≲zs = ≲-trans true  xs ys zs s₁    s₂    xs≲ys ys≲zs
-- ≲-trans true (1ᵇ xs) (1ᵇ ys) (2ᵇ zs) s₁    s₂ xs≲ys ys≲zs = ≲-trans true  xs ys zs s₁    true  xs≲ys ys≲zs
-- ≲-trans true (1ᵇ xs) (2ᵇ ys) (1ᵇ zs) s₁    s₂ xs≲ys ys≲zs = ≲-trans true  xs ys zs true  false xs≲ys ys≲zs
-- ≲-trans true (1ᵇ xs) (2ᵇ ys) (2ᵇ zs) s₁    s₂ xs≲ys ys≲zs = ≲-trans true  xs ys zs true  s₂    xs≲ys ys≲zs
-- ≲-trans true (2ᵇ xs) (1ᵇ ys) (1ᵇ zs) s₁    s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs false s₂    xs≲ys ys≲zs
-- ≲-trans true (2ᵇ xs) (1ᵇ ys) (2ᵇ zs) s₁    s₂ xs≲ys ys≲zs = ≲-trans true  xs ys zs false true  xs≲ys ys≲zs
-- ≲-trans true (2ᵇ xs) (2ᵇ ys) (1ᵇ zs) false s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs false false xs≲ys ys≲zs
-- ≲-trans true (2ᵇ xs) (2ᵇ ys) (1ᵇ zs) true  s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs true  false xs≲ys ys≲zs
-- ≲-trans true (2ᵇ xs) (2ᵇ ys) (2ᵇ zs) s₁    s₂ xs≲ys ys≲zs = ≲-trans true  xs ys zs s₁    s₂    xs≲ys ys≲zs
-- ≲-trans false 0ᵇ (1ᵇ ys) (1ᵇ zs) false s₂ xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ (1ᵇ ys) (2ᵇ zs) false s₂ xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ (2ᵇ ys) (1ᵇ zs) false s₂ xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ (2ᵇ ys) (2ᵇ zs) false s₂ xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ 0ᵇ zs true false xs≲ys ys≲zs = ys≲zs
-- ≲-trans false 0ᵇ (1ᵇ ys) (1ᵇ zs) true false xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ (1ᵇ ys) (2ᵇ zs) true false xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ (2ᵇ ys) (1ᵇ zs) true false xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ (2ᵇ ys) (2ᵇ zs) true false xs≲ys ys≲zs = tt
-- ≲-trans false 0ᵇ ys zs true true xs≲ys ys≲zs = tt
-- ≲-trans false (1ᵇ xs) (1ᵇ ys) (1ᵇ zs) false s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs false s₂ xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (1ᵇ ys) (2ᵇ zs) false s₂ xs≲ys ys≲zs = ≲-trans true xs ys zs false true xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (2ᵇ ys) (1ᵇ zs) false s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs true false xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (2ᵇ ys) (2ᵇ zs) false s₂ xs≲ys ys≲zs = ≲-trans true xs ys zs true s₂ xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (1ᵇ ys) (1ᵇ zs) true s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs true s₂ xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (1ᵇ ys) (2ᵇ zs) true s₂ xs≲ys ys≲zs = ≲-trans true xs ys zs true true xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (2ᵇ ys) (1ᵇ zs) true false xs≲ys ys≲zs = ≲-trans false xs ys zs true false xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (2ᵇ ys) (1ᵇ zs) true true xs≲ys ys≲zs = ≲-trans true xs ys zs true false xs≲ys ys≲zs
-- ≲-trans false (1ᵇ xs) (2ᵇ ys) (2ᵇ zs) true s₂ xs≲ys ys≲zs = ≲-trans true xs ys zs true s₂ xs≲ys ys≲zs
-- ≲-trans false (2ᵇ xs) (1ᵇ ys) (1ᵇ zs) s₁ s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs false s₂ xs≲ys ys≲zs
-- ≲-trans false (2ᵇ xs) (1ᵇ ys) (2ᵇ zs) false s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs false true xs≲ys ys≲zs
-- ≲-trans false (2ᵇ xs) (1ᵇ ys) (2ᵇ zs) true false xs≲ys ys≲zs = ≲-trans false xs ys zs false true xs≲ys ys≲zs
-- ≲-trans false (2ᵇ xs) (1ᵇ ys) (2ᵇ zs) true true xs≲ys ys≲zs = ≲-trans true xs ys zs false true xs≲ys ys≲zs
-- ≲-trans false (2ᵇ xs) (2ᵇ ys) (1ᵇ zs) false s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs false false xs≲ys ys≲zs
-- ≲-trans false (2ᵇ xs) (2ᵇ ys) (1ᵇ zs) true s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs true false xs≲ys ys≲zs
-- ≲-trans false (2ᵇ xs) (2ᵇ ys) (2ᵇ zs) s₁ s₂ xs≲ys ys≲zs = ≲-trans false xs ys zs s₁ s₂ xs≲ys ys≲zs
