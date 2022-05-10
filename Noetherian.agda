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

