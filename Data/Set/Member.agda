module Data.Set.Member where

open import Prelude
open import Data.Set.Definition
open import Data.Set.Eliminators


-- module _ {A : Type a} where
--   _∈_ : A → 𝒦 A → Type a
--   _∈_ = λ x → fst ∘′ ⟦ ∈-alg x ⟧
--     where
--     ∈-alg : A → ψ A (hProp a)
--     ∈-alg = {!!}
