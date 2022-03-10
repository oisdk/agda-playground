module Graphs where

open import Prelude
open import Data.List
open import Noetherian
open import Data.List.Membership

GraphOf : Type a → Type a
GraphOf A = A → List A

module _ {A : Type a} (noeth : Noetherian A) (_≟_ : Discrete A) where
  open WithDecEq _≟_


  dfs : GraphOf A → GraphOf A
  dfs g r = f (r ∷ []) [] noeth
    where
    f : List A → (seen : List A) → NoethAcc seen → List A
    f []       seen a = []
    f (r ∷ rs) seen a with r ∈? seen
    ... | yes r∈seen = f rs seen a
    f (r ∷ rs) seen (noeth-acc wf) | no r∉seen = r ∷ f (g r ++ rs) (r ∷ seen) (wf r r∉seen)
