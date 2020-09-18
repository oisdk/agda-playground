{-# OPTIONS --cubical --safe #-}

module Data.Binary.Equatable where

open import Prelude
open import Data.Binary.Definition

infix 4 _≡ᴮ_
_≡ᴮ_ : 𝔹 → 𝔹 → Bool
[] ≡ᴮ [] = true
[] ≡ᴮ (1ᵇ∷ ys) = false
[] ≡ᴮ (2ᵇ∷ ys) = false
(1ᵇ∷ xs) ≡ᴮ [] = false
(1ᵇ∷ xs) ≡ᴮ (1ᵇ∷ ys) = xs ≡ᴮ ys
(1ᵇ∷ xs) ≡ᴮ (2ᵇ∷ ys) = false
(2ᵇ∷ xs) ≡ᴮ [] = false
(2ᵇ∷ xs) ≡ᴮ (1ᵇ∷ ys) = false
(2ᵇ∷ xs) ≡ᴮ (2ᵇ∷ ys) = xs ≡ᴮ ys

𝔹-eq-true : ∀ xs ys → T (xs ≡ᴮ ys) → xs ≡ ys
𝔹-eq-true []       []       xs≡ys i = []
𝔹-eq-true (1ᵇ∷ xs) (1ᵇ∷ ys) xs≡ys i = 1ᵇ∷ 𝔹-eq-true xs ys xs≡ys i
𝔹-eq-true (2ᵇ∷ xs) (2ᵇ∷ ys) xs≡ys i = 2ᵇ∷ 𝔹-eq-true xs ys xs≡ys i

case𝔹 : A → A → A → 𝔹 → A
case𝔹 x y z [] = x
case𝔹 x y z (1ᵇ∷ xs) = y
case𝔹 x y z (2ᵇ∷ xs) = z

tail𝔹 : 𝔹 → 𝔹
tail𝔹 [] = []
tail𝔹 (1ᵇ∷ xs) = xs
tail𝔹 (2ᵇ∷ xs) = xs

𝔹-eq-false : ∀ xs ys → T (not (xs ≡ᴮ ys)) → xs ≢ ys
𝔹-eq-false []       (1ᵇ∷ ys) p xs≡ys = subst (case𝔹 ⊤ ⊥ ⊥) xs≡ys tt
𝔹-eq-false []       (2ᵇ∷ ys) p xs≡ys = subst (case𝔹 ⊤ ⊥ ⊥) xs≡ys tt
𝔹-eq-false (1ᵇ∷ xs) []       p xs≡ys = subst (case𝔹 ⊥ ⊤ ⊥) xs≡ys tt
𝔹-eq-false (1ᵇ∷ xs) (1ᵇ∷ ys) p xs≡ys = 𝔹-eq-false xs ys p (cong tail𝔹 xs≡ys)
𝔹-eq-false (1ᵇ∷ xs) (2ᵇ∷ ys) p xs≡ys = subst (case𝔹 ⊥ ⊤ ⊥) xs≡ys tt
𝔹-eq-false (2ᵇ∷ xs) []       p xs≡ys = subst (case𝔹 ⊥ ⊥ ⊤) xs≡ys tt
𝔹-eq-false (2ᵇ∷ xs) (1ᵇ∷ ys) p xs≡ys = subst (case𝔹 ⊥ ⊥ ⊤) xs≡ys tt
𝔹-eq-false (2ᵇ∷ xs) (2ᵇ∷ ys) p xs≡ys = 𝔹-eq-false xs ys p (cong tail𝔹 xs≡ys)

𝔹-reflect-eq : ∀ xs ys → Reflects (xs ≡ ys) (xs ≡ᴮ ys)
𝔹-reflect-eq xs ys with xs ≡ᴮ ys | inspect (xs ≡ᴮ_) ys
𝔹-reflect-eq xs ys | false | 〖 e 〗 = 𝔹-eq-false xs ys (subst T (sym (cong not e)) tt)
𝔹-reflect-eq xs ys | true  | 〖 e 〗 = 𝔹-eq-true xs ys (subst T (sym e) tt)

_≟_ : Discrete 𝔹
(xs ≟ ys) .does = xs ≡ᴮ ys
(xs ≟ ys) .why = 𝔹-reflect-eq xs ys
