{-# OPTIONS --safe #-}

open import Prelude hiding (_↔_)

module Data.Permutation.NonNorm {A : Type a} (_≟_ : Discrete A) where

open import Data.Permutation.Swap _≟_

open import Data.List hiding ([]; _∷_)
import Data.List as ConsR

Swaps : Type a
Swaps = List (A × A)

infixl 5 _∘⟨_⟩
pattern _∘⟨_⟩ xs x = x ConsR.∷ xs

pattern ⟨⟩ = ConsR.[]

infixr 4.5 _·_
_·_ : Swaps → A → A
_·_ = flip (foldl (flip (uncurry _↔_·_)))

-- We can't really compute the support without first removing ids from the list
-- 
-- supp-swaps : Swaps → List A
-- supp-swaps = foldr (λ { (x , y) xs → xs ∘⟨ y ⟩ ∘⟨ x ⟩ }) ⟨⟩

swap-inj : ∀ x y z₁ z₂ → x ↔ y · z₁ ≡ x ↔ y · z₂ → z₁ ≡ z₂
swap-inj x y z₁ z₂ p with does (x ≟ z₁)
                        | why  (x ≟ z₁)
                        | does (x ≟ z₂)
                        | why  (x ≟ z₂)
                        | does (y ≟ z₁)
                        | why  (y ≟ z₁)
                        | does (y ≟ z₂)
                        | why  (y ≟ z₂)
... | true | x≡z₁ | true | x≡z₂ | _ | _ | _ | _ = sym x≡z₁ ; x≡z₂
... | _ | _ | _ | _ | true | y≡z₁ | true | y≡z₂ = sym y≡z₁ ; y≡z₂
... | false | _ | false | _ | false | _ | false | _ = p
... | false | x≢z₁ | false | _ | false | _ | true | _ = ⊥-elim (x≢z₁ (sym p))
... | false | _ | false | x≢z₂ | true | _ | false | _ = ⊥-elim (x≢z₂ p)
... | false | _ | true | _ | false | y≢z₁ | _ | _ = ⊥-elim (y≢z₁ (sym p))
... | false | x≢z₁ | true | _ | true | y≡z₁ | _ | _ = ⊥-elim (x≢z₁ (p ; y≡z₁))
... | true | _ | false | x≢z₁ | true | _ | false | y≢z₂ = ⊥-elim (y≢z₂ p)
... | true | _ | false | _ | false | _ | false | y≢z₂ = ⊥-elim (y≢z₂ p)
... | true | x≡z₁ | false | x≢z₂ | false | y≢z₁ | true | y≡z₂ = ⊥-elim (y≢z₁ (p ; x≡z₁))

perm-inj : ∀ xs z₁ z₂ → xs · z₁ ≡ xs · z₂ → z₁ ≡ z₂
perm-inj ⟨⟩              z₁ z₂ p = p
perm-inj (xs ∘⟨ x , y ⟩) z₁ z₂ p =
  swap-inj x y z₁ z₂ (perm-inj xs (x ↔ y · z₁) (x ↔ y · z₂) p)

infixl 6 _∙_
_∙_ : Swaps → Swaps → Swaps
xs ∙ ys = ys ++ xs

open import Path.Reasoning
open import Data.List.Properties

∙-· : ∀ xs ys n → xs ∙ ys · n ≡ xs · ys · n
∙-· xs ys n = foldl-++ (flip (uncurry _↔_·_)) n ys xs

neg : Swaps → Swaps
neg = reverse

open import Path.Reasoning

-- neg-id : ∀ xs n → xs ∙ neg xs · n ≡ n
-- neg-id xs n =
--   xs ∙ neg xs · n ≡⟨⟩
--   neg xs ++ xs · n ≡⟨ foldl-++ (flip (uncurry _↔_·_)) n (neg xs) xs ⟩
--   foldl (flip (uncurry _↔_·_)) (neg xs · n) xs ≡⟨⟩
--   foldl (flip (uncurry _↔_·_)) (foldl (flip (uncurry _↔_·_)) n (neg xs)) xs ≡⟨⟩
--   foldl (flip (uncurry _↔_·_)) (foldl (flip (uncurry _↔_·_)) n (foldl _∘⟨_⟩ ⟨⟩ xs)) xs ≡⟨ {!!} ⟩
--   foldl (flip (uncurry _↔_·_)) (foldr (uncurry _↔_·_) n xs) xs ≡⟨ {!!} ⟩
--   n ∎
  
