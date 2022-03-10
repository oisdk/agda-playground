module Noetherian where

open import Prelude
open import Data.List
open import Data.List.Membership

data NoethAcc {A : Type a} (xs : List A) : Type a where
  noeth-acc : (∀ x → x ∉ xs → NoethAcc (x ∷ xs)) → NoethAcc xs

Noetherian : Type a → Type a
Noetherian A = NoethAcc {A = A} []
