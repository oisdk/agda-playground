{-# OPTIONS --cubical --safe #-}

module Data.List.Filter where

open import Prelude
open import Data.List
open import Data.List.Membership
open import Data.Sigma.Properties
open import Data.Bool.Properties
open import Data.Fin

module _ {p} {P : A → Type p} where
  filter : (P? : ∀ x → Dec (P x)) → List A → List (∃ P)
  filter P? = foldr f []
    where
    f : _ → List (∃ P) → List (∃ P)
    f y ys with P? y
    ... | yes t = (y , t) ∷ ys
    ... | no _  = ys

  filter-preserves : (isPropP : ∀ x → isProp (P x)) (P? : ∀ x → Dec (P x)) (xs : List A) →
                     (x : A) →
                     (v : P x) →
                     (x ∈ xs) →
                     ((x , v) ∈ filter P? xs)
  filter-preserves isPropP P? (x ∷ xs) y v (n , y∈xs) with P? x
  filter-preserves isPropP P? (x ∷ xs) y v (f0   , y∈xs) | yes t = f0 , ΣProp≡ isPropP y∈xs
  filter-preserves isPropP P? (x ∷ xs) y v (fs n , y∈xs) | yes t = let m , q = filter-preserves isPropP P? xs y v (n , y∈xs) in fs m , q
  filter-preserves isPropP P? (x ∷ xs) y v (f0   , y∈xs) | no ¬t = ⊥-elim (¬t (subst P (sym y∈xs) v))
  filter-preserves isPropP P? (x ∷ xs) y v (fs n , y∈xs) | no ¬t = filter-preserves isPropP P? xs y v (n , y∈xs)
