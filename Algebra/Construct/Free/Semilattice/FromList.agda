{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.FromList where

open import Prelude
open import Algebra.Construct.Free.Semilattice.Definition
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Relation.Unary
open import Data.List
import Data.List.Membership as ℰ
open import Data.Fin using (Fin; fs; f0)
open import HITs.PropositionalTruncation.Sugar
open import HITs.PropositionalTruncation.Properties

fromList : List A → 𝒦 A
fromList = foldr _∷_ []

∈List⇒∈𝒦 : ∀ xs {x : A} → ∥ x ℰ.∈ xs ∥ → x ∈ fromList xs
∈List⇒∈𝒦 [] ∣x∈xs∣ = ⊥-elim (refute-trunc (λ ()) ∣x∈xs∣)
∈List⇒∈𝒦 (x ∷ xs) ∣x∈xs∣ = do
  (fs n , x∈xs) ← ∣x∈xs∣
    where (f0 , x∈xs) → ∣ inl x∈xs ∣
  ∣ inr (∈List⇒∈𝒦 xs ∣ n , x∈xs ∣) ∣
