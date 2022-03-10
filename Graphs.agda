module Graphs where

open import Prelude
open import Data.List hiding (tabulate)
open import Noetherian
open import Data.List.Membership
open import Codata.Stream

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


  ids⊙ : GraphOf A → ℕ → A → (∀ {seen : List A} → NoethFrom seen → List A) → (∀ {seen : List A} → NoethFrom seen → List A)
  ids⊙ g n r q wf with wf r
  ids⊙ g n       r q wf | done _   = q wf
  ids⊙ g zero    r q wf | more _ a = r ∷ q a
  ids⊙ g (suc n) r q wf | more _ a = foldr (ids⊙ g n) q (g r) a

  ids : GraphOf A → ℕ → GraphOf A
  ids g n r = ids⊙ g n r (λ _ → []) noeth

  bfs : GraphOf A → A → Stream (List A)
  bfs g r = tabulate (flip (ids g) r)
