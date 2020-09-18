{-# OPTIONS --cubical --safe #-}

module Data.Binary.Order where

open import Prelude
open import Data.Binary.Definition

infix 4 _≲ᴮ_&_
_≲ᴮ_&_ : 𝔹 → 𝔹 → Bool → Bool
[]     ≲ᴮ ys     & true  = true
[]     ≲ᴮ []     & false = false
[]     ≲ᴮ 1ᵇ∷ ys & false = true
[]     ≲ᴮ 2ᵇ∷ ys & false = true
1ᵇ∷ xs ≲ᴮ []     & s     = false
1ᵇ∷ xs ≲ᴮ 1ᵇ∷ ys & s     = xs ≲ᴮ ys & s
1ᵇ∷ xs ≲ᴮ 2ᵇ∷ ys & s     = xs ≲ᴮ ys & true
2ᵇ∷ xs ≲ᴮ []     & s     = false
2ᵇ∷ xs ≲ᴮ 1ᵇ∷ ys & s     = xs ≲ᴮ ys & false
2ᵇ∷ xs ≲ᴮ 2ᵇ∷ ys & s     = xs ≲ᴮ ys & s

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

weaken : ∀ xs ys → T (xs ≲ᴮ ys & false) → T (xs ≲ᴮ ys & true)
weaken [] ys xs≲ys = tt
weaken (1ᵇ∷ x) [] xs≲ys = xs≲ys
weaken (1ᵇ∷ x) (1ᵇ∷ x₁) xs≲ys = weaken x x₁ xs≲ys
weaken (1ᵇ∷ x) (2ᵇ∷ x₁) xs≲ys = xs≲ys
weaken (2ᵇ∷ x) [] xs≲ys = xs≲ys
weaken (2ᵇ∷ x) (1ᵇ∷ x₁) xs≲ys = xs≲ys
weaken (2ᵇ∷ x) (2ᵇ∷ x₁) xs≲ys = weaken x x₁ xs≲ys

≲-trans : ∀ xs ys zs s₁ s₂ → T (xs ≲ᴮ ys & s₁) → T (ys ≲ᴮ zs & s₂) → T (xs ≲ᴮ zs & (s₁ and s₂))
≲-trans [] (1ᵇ∷ ys) (1ᵇ∷ zs) false s₂ xs≲ys ys≲zs = tt
≲-trans [] (1ᵇ∷ ys) (2ᵇ∷ zs) false s₂ xs≲ys ys≲zs = tt
≲-trans [] (2ᵇ∷ ys) (1ᵇ∷ zs) false s₂ xs≲ys ys≲zs = tt
≲-trans [] (2ᵇ∷ ys) (2ᵇ∷ zs) false s₂ xs≲ys ys≲zs = tt
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (1ᵇ∷ zs) false false xs≲ys ys≲zs = ≲-trans xs ys zs false false xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (1ᵇ∷ zs) false true xs≲ys ys≲zs = ≲-trans xs ys zs false true xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (2ᵇ∷ ys) (1ᵇ∷ zs) false s₂ xs≲ys ys≲zs = ≲-trans xs ys zs true false xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) [] [] false s₂ xs≲ys ys≲zs = xs≲ys
≲-trans (2ᵇ∷ []) [] (1ᵇ∷ x) false s₂ xs≲ys ys≲zs = ≲-trans [] [] x false true xs≲ys tt
≲-trans (2ᵇ∷ 1ᵇ∷ x) [] (1ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans (1ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ 2ᵇ∷ x) [] (1ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans (2ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ []) [] (2ᵇ∷ x) false s₂ xs≲ys ys≲zs = ≲-trans [] [] x false true xs≲ys tt
≲-trans (2ᵇ∷ 1ᵇ∷ x) [] (2ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans (1ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ 2ᵇ∷ x) [] (2ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans (2ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ xs) (1ᵇ∷ x) [] false s₂ xs≲ys ys≲zs = ys≲zs
≲-trans (2ᵇ∷ xs) (1ᵇ∷ x) (1ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans xs x x₁ false s₂ xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (1ᵇ∷ x) (2ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans xs x x₁ false true xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ x) [] false s₂ xs≲ys ys≲zs = ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ x) (1ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans xs x x₁ false false xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ x) (2ᵇ∷ x₁) false s₂ xs≲ys ys≲zs = ≲-trans xs x x₁ false s₂ xs≲ys ys≲zs
≲-trans [] [] (1ᵇ∷ zs) true false xs≲ys ys≲zs = tt
≲-trans [] [] (2ᵇ∷ zs) true false xs≲ys ys≲zs = tt
≲-trans [] (1ᵇ∷ ys) (1ᵇ∷ zs) true false xs≲ys ys≲zs = tt
≲-trans [] (1ᵇ∷ ys) (2ᵇ∷ zs) true false xs≲ys ys≲zs = tt
≲-trans [] (2ᵇ∷ ys) (1ᵇ∷ zs) true false xs≲ys ys≲zs = tt
≲-trans [] (2ᵇ∷ ys) (2ᵇ∷ zs) true false xs≲ys ys≲zs = tt
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (1ᵇ∷ zs) true false xs≲ys ys≲zs = ≲-trans xs ys zs true false xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (2ᵇ∷ zs) true false xs≲ys ys≲zs = ≲-trans xs ys zs true true xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (2ᵇ∷ ys) (1ᵇ∷ zs) true false xs≲ys ys≲zs = ≲-trans xs ys zs true false xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) [] [] true false xs≲ys ys≲zs = ys≲zs
≲-trans (2ᵇ∷ []) [] (1ᵇ∷ x) true false xs≲ys ys≲zs = ≲-trans [] [] x false true xs≲ys tt
≲-trans (2ᵇ∷ 1ᵇ∷ x) [] (1ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans (1ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ 2ᵇ∷ x) [] (1ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans (2ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ []) [] (2ᵇ∷ x) true false xs≲ys ys≲zs = ≲-trans [] [] x false true xs≲ys tt
≲-trans (2ᵇ∷ 1ᵇ∷ x) [] (2ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans (1ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ 2ᵇ∷ x) [] (2ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans (2ᵇ∷ x) [] x₁ false true xs≲ys tt
≲-trans (2ᵇ∷ xs) (1ᵇ∷ x) [] true false xs≲ys ys≲zs = ys≲zs
≲-trans (2ᵇ∷ xs) (1ᵇ∷ x) (1ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans xs x x₁ false false xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (1ᵇ∷ x) (2ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans xs x x₁ false true xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ x) [] true false xs≲ys ys≲zs = ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ x) (1ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans xs x x₁ true false xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ x) (2ᵇ∷ x₁) true false xs≲ys ys≲zs = ≲-trans xs x x₁ true false xs≲ys ys≲zs
≲-trans [] ys zs true true xs≲ys ys≲zs = tt
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) [] true true xs≲ys ys≲zs = ys≲zs
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (1ᵇ∷ x) true true xs≲ys ys≲zs = ≲-trans xs ys x true true xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (2ᵇ∷ x) true true xs≲ys ys≲zs = ≲-trans xs ys x true true xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (2ᵇ∷ ys) (2ᵇ∷ zs) true true xs≲ys ys≲zs = ≲-trans xs ys zs true true xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (1ᵇ∷ ys) (1ᵇ∷ zs) true true xs≲ys ys≲zs = ≲-trans xs ys zs false true xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ ys) [] true true xs≲ys ys≲zs = ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ ys) (1ᵇ∷ x) true true xs≲ys ys≲zs = ≲-trans xs ys x true false xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (2ᵇ∷ ys) (2ᵇ∷ zs) false true xs≲ys ys≲zs = ≲-trans xs ys zs true true xs≲ys ys≲zs
≲-trans (2ᵇ∷ xs) (2ᵇ∷ ys) (2ᵇ∷ x) true true xs≲ys ys≲zs = ≲-trans xs ys x true true xs≲ys ys≲zs
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (2ᵇ∷ zs) false false xs≲ys ys≲zs = weaken xs zs (≲-trans xs ys zs false true xs≲ys ys≲zs)
≲-trans (1ᵇ∷ xs) (1ᵇ∷ ys) (2ᵇ∷ zs) false true  xs≲ys ys≲zs = weaken xs zs (≲-trans xs ys zs false true xs≲ys ys≲zs)
≲-trans (1ᵇ∷ xs) (2ᵇ∷ ys) (2ᵇ∷ zs) false false xs≲ys ys≲zs = weaken xs zs (≲-trans xs ys zs true false xs≲ys ys≲zs)
≲-trans (1ᵇ∷ xs) (2ᵇ∷ ys) (2ᵇ∷ zs) true  false xs≲ys ys≲zs = weaken xs zs (≲-trans xs ys zs true false xs≲ys ys≲zs)
≲-trans (1ᵇ∷ xs) (2ᵇ∷ ys) (1ᵇ∷ zs) true  true  xs≲ys ys≲zs = weaken xs zs (≲-trans xs ys zs true false xs≲ys ys≲zs)
≲-trans (2ᵇ∷ xs) (1ᵇ∷ ys) (2ᵇ∷ zs) true  true  xs≲ys ys≲zs = weaken xs zs (≲-trans xs ys zs false true xs≲ys ys≲zs)
