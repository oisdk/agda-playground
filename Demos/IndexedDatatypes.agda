module Demos.IndexedDatatypes where

open import Level
open import Data.Nat
open import Data.Bool hiding (T)
open import Data.Unit
open import Data.Empty
open import Relation.Nullary.Decidable hiding (T?)
open import Function using (id; _∘_)

private variable n m : ℕ

module BadVersion where
  data _≤_ : ℕ → ℕ → Type where
    z≤n : 0 ≤ n
    s≤s : n ≤ m → suc n ≤ suc m

  ≤-pred : suc n ≤ suc m → n ≤ m
  ≤-pred (s≤s p) = p

  _≤?_ : ∀ n m → Dec (n ≤ m)
  zero  ≤? m = yes z≤n
  suc n ≤? zero = no (λ ())
  suc n ≤? suc m with n ≤? m
  ... | yes n≤m = yes (s≤s n≤m)
  ... | no  n≰m = no (n≰m ∘ ≤-pred)

-- Usually defined in Data.Bool
T : Bool → Type
T true  = ⊤
T false = ⊥

T? : ∀ b → Dec (T b)
T? false = no id
T? true  = yes tt

module GoodVersion where
  _≤ᴮ_ : ℕ → ℕ → Bool
  zero  ≤ᴮ m     = true
  suc n ≤ᴮ zero  = false
  suc n ≤ᴮ suc m = n ≤ᴮ m

  _≤_ : ℕ → ℕ → Type
  n ≤ m = T (n ≤ᴮ m)

  _≤?_ : ∀ n m → Dec (n ≤ m)
  n ≤? m = T? (n ≤ᴮ m)

  
