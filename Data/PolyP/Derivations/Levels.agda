{-# OPTIONS --cubical --safe --guardedness #-}

module Data.PolyP.Derivations.Levels where

open import Data.PolyP
open import Level hiding (Type) renaming (Type₀ to Type)
open import Data.PolyP.Types
open import Data.Sum
open import Data.Sigma
open import Data.Unit
open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Function
open import Literals.Number
open import Data.Fin.Literals
open import Data.Nat.Literals

levels : ⟦ FOREST ⟧ ~ A → ⟦ LEVELS ⟧ ~ A
levels t = go t []′
  where
  go : ⟦ FOREST ⟧ ~ A → ⟦ LEVELS ⟧ ~ A → ⟦ LEVELS ⟧ ~ A
  go =
    cata λ xs zs →
      cata (λ  { (inl _                             )  → zs
               ; (inr (inl _         ,  qs       )  )  → qs
               ; (inr (inr (x , xs)  ,  []′      )  )  → (x ∷′ []′  ) ∷′ xs []′
               ; (inr (inr (x , xs)  ,  q ∷′ qs  )  )  → (x ∷′ q    ) ∷′ xs qs
               }) xs
