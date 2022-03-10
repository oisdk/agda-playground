module Noetherian where

open import Prelude
open import Data.List
open import Data.List.Membership
open import Data.List.Properties using (is-empty)

module NonDec where
  data NoethAcc {A : Type a} (xs : List A) : Type a where
    noeth-acc : (∀ x → x ∉ xs → NoethAcc (x ∷ xs)) → NoethAcc xs

  Noetherian : Type a → Type a
  Noetherian A = NoethAcc {A = A} []

module Decidable where
  NoethFrom : List A → Type _
  data NoethAcc {A : Type a} (x : A) (xs : List A) : Type a

  data NoethAcc x xs where
    done : x ∈ xs → NoethAcc x xs
    more : x ∉ xs → NoethFrom (x ∷ xs) → NoethAcc x xs

  NoethFrom xs = ∀ x → NoethAcc x xs

  Noetherian : Type a → Type a
  Noetherian A = NoethFrom {A = A} []

-- open import WellFounded
-- open NonDec

-- module ToWellFounded {A : Type a} (_≟_ : Discrete A) where
--   rem-may : A → List A → Maybe (List A)
--   rem-may x = uncurry (bool (const nothing) just) ∘ foldr f (false , [])
--     where
--     f : A → Bool × List A → Bool × List A
--     f y ys = let p = x ≟ y in does p or fst ys , (if does p then snd ys else y ∷ snd ys)

--   _≺ᴮ_ : List A → List A → Bool
--   xs ≺ᴮ ys = maybe false (not ∘ is-empty) (foldr (λ y → maybe nothing (rem-may y) ) (just xs) ys)


--   _≺_ : List A → List A → Type
--   xs ≺ ys = T (xs ≺ᴮ ys)

--   to-wf : ∀ {xs : List A} → NoethAcc xs → Acc _≺_ xs
--   to-wf na = acc (go _ na)
--     where
--     go : ∀ xs → NoethAcc xs → ∀ ys → ys ≺ xs → Acc _≺_ ys
--     go []       na (y ∷ ys) p = {!!}
--     go (x ∷ xs) na ys p = {!!}
