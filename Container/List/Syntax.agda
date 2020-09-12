{-# OPTIONS --cubical --safe #-}

module Container.List.Syntax where

open import Prelude
open import Container
open import Container.List
open import Data.Fin

record ListSyntax {a b} (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  field [_] : B → List A

open ListSyntax ⦃ ... ⦄ public

instance
  cons : ⦃ _ : ListSyntax A B ⦄ →  ListSyntax A (A × B)
  [_] ⦃ cons ⦄ (x , xs) .fst = suc ([ xs ] .fst)
  [_] ⦃ cons ⦄ (x , xs) .snd f0 = x
  [_] ⦃ cons ⦄ (x , xs) .snd (fs n) = [ xs ] .snd n

instance
  sing : ListSyntax A A
  [_] ⦃ sing ⦄ x = 1 , const x


