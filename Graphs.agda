module Graphs where

open import Prelude
open import Data.List
open import Noetherian
open import Data.List.Membership

open Decidable

GraphOf : Type a → Type a
GraphOf A = A → List A

module _ {A : Type a} (noeth : Noetherian A) where
  dfs : GraphOf A → GraphOf A
  dfs g r = f (r ∷ []) noeth
    where
    f : List A → {seen : List A} → NoethFrom seen → List A
    f []       _ = []
    f (r ∷ rs) wf with wf r
    ... | done _   = f rs wf
    ... | more _ a = r ∷ f (g r ++ rs) a
