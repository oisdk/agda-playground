module Data.Set.Member where

open import Prelude hiding (⊥)
open import Data.Set.Definition
open import Data.Set.Eliminators
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Properties
open import Data.Sigma.Properties
open import HITs.PropositionalTruncation.Sugar

module _ {a} {A : Type a} (x : A) where
  open import Data.Set.Any (x ≡_)
    public
    renaming (_◇_ to _∈_)

module WithDecEq (_≟_ : Discrete A) where

  _\\_ : 𝒦 A → A → 𝒦 A
  xs \\ x = remove x (_≟_ x) xs

  _∈?_ : ∀ (x : A) xs → Dec (x ∈ xs)
  _∈?_ x = ◇? x (_≟_ x)
