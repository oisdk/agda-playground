{-# OPTIONS --cubical --safe #-}

module Data.Binary.Subtraction where

open import Data.Binary.Definition
open import Prelude

dec′ : 𝔹 → 𝔹
dec : 𝔹 → 𝔹

dec′ 0ᵇ = 0ᵇ
dec′ (1ᵇ xs) = 2ᵇ dec′ xs
dec′ (2ᵇ xs) = 2ᵇ 1ᵇ xs

dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = dec′ xs

r′ : 𝔹 → 𝔹
r′ 0ᵇ = 0ᵇ
r′ (1ᵇ xs) = 1ᵇ xs
r′ (2ᵇ xs) = 2ᵇ (1ᵇ xs)

r″ : 𝔹 → 𝔹
r″ 0ᵇ = 0ᵇ
r″ (1ᵇ xs) = 2ᵇ xs
r″ (2ᵇ xs) = 2ᵇ (2ᵇ xs)

r : 𝔹 → Maybe 𝔹
r 0ᵇ = nothing
r (1ᵇ xs) = just xs
r (2ᵇ xs) = just (2ᵇ xs)

unzero : Maybe 𝔹 → 𝔹
unzero nothing = 0ᵇ
unzero (just x) = x

map : (𝔹 → 𝔹) → Maybe 𝔹 → Maybe 𝔹
map f nothing = nothing
map f (just x) = just (f x)

sub₄ : 𝔹 → 𝔹 → 𝔹
sub₃ : 𝔹 → 𝔹 → 𝔹

sub₄ 0ᵇ         ys      = 0ᵇ
sub₄ (1ᵇ xs)    (1ᵇ ys) = r″ (sub₄ xs ys)
sub₄ (2ᵇ xs)    (2ᵇ ys) = r″ (sub₄ xs ys)
sub₄ (1ᵇ xs)    (2ᵇ ys) = r′ (sub₄ xs ys)
sub₄ (2ᵇ xs)    (1ᵇ ys) = r′ (sub₃ xs ys)
sub₄ (1ᵇ 0ᵇ)    0ᵇ      = 1ᵇ 0ᵇ
sub₄ (1ᵇ 1ᵇ xs) 0ᵇ      = 2ᵇ (1ᵇ (dec′ xs))
sub₄ (1ᵇ 2ᵇ xs) 0ᵇ      = 2ᵇ (1ᵇ (1ᵇ xs))
sub₄ (2ᵇ xs)    0ᵇ      = 2ᵇ (dec′ xs)

sub₃ 0ᵇ      0ᵇ      = 1ᵇ 0ᵇ
sub₃ 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₃ 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₃ (1ᵇ xs) 0ᵇ      = 2ᵇ (dec′ xs)
sub₃ (2ᵇ xs) 0ᵇ      = 2ᵇ (1ᵇ xs)
sub₃ (1ᵇ xs) (1ᵇ ys) = r′ (sub₃ xs ys)
sub₃ (2ᵇ xs) (2ᵇ ys) = r′ (sub₃ xs ys)
sub₃ (1ᵇ xs) (2ᵇ ys) = r″ (sub₄ xs ys)
sub₃ (2ᵇ xs) (1ᵇ ys) = r″ (sub₃ xs ys)

sub₂ : 𝔹 → 𝔹 → Maybe 𝔹
sub₂ 0ᵇ      ys      = nothing
sub₂ (1ᵇ xs) 0ᵇ      = just (dec′ xs)
sub₂ (2ᵇ xs) 0ᵇ      = just (1ᵇ xs)
sub₂ (1ᵇ xs) (1ᵇ ys) = map 1ᵇ_ (sub₂ xs ys)
sub₂ (2ᵇ xs) (2ᵇ ys) = map 1ᵇ_ (sub₂ xs ys)
sub₂ (1ᵇ xs) (2ᵇ ys) = r (sub₄ xs ys)
sub₂ (2ᵇ xs) (1ᵇ ys) = r (sub₃ xs ys)

sub₁ : 𝔹 → 𝔹 → Maybe 𝔹
sub₁ xs      0ᵇ      = just xs
sub₁ 0ᵇ      (1ᵇ ys) = nothing
sub₁ 0ᵇ      (2ᵇ ys) = nothing
sub₁ (1ᵇ xs) (1ᵇ ys) = r (sub₃ xs ys)
sub₁ (2ᵇ xs) (2ᵇ ys) = r (sub₃ xs ys)
sub₁ (2ᵇ xs) (1ᵇ ys) = map 1ᵇ_ (sub₁ xs ys)
sub₁ (1ᵇ xs) (2ᵇ ys) = map 1ᵇ_ (sub₂ xs ys)

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
xs - ys = unzero (sub₁ xs ys)

open import Data.Binary.Testers
import Data.Nat as ℕ
open import Prelude

_ : test _-_ ℕ._∸_ 30
_ = refl
