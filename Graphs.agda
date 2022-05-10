module Graphs where

open import Prelude
open import Data.List hiding (tabulate)
open import Noetherian
open import Data.List.Membership
open import Codata.Stream

open Decidable

GraphOf : Type a → Type a
GraphOf A = A → List A

module _ (g : GraphOf A) where
  dfs⊙ : {seen : List A} → NoethFrom seen → A → List A → List A
  dfs⊙ nf x xs with nf x
  ... | done _           = xs
  ... | more x∉seen step = x ∷ foldr (dfs⊙ step) xs (g x)

  ids⊙ : ℕ → A → (∀ {seen : List A} → NoethFrom seen → List A) → (∀ {seen : List A} → NoethFrom seen → List A)
  ids⊙ n r q wf with wf r
  ids⊙ n       r q wf | done _   = q wf
  ids⊙ zero    r q wf | more _ a = r ∷ q a
  ids⊙ (suc n) r q wf | more _ a = foldr (ids⊙ n) q (g r) a

module _ (noeth : Noetherian A) where
  dfs : GraphOf A → GraphOf A
  dfs g x = dfs⊙ g noeth x []

  ids : GraphOf A → ℕ → GraphOf A
  ids g n r = ids⊙ g n r (λ _ → []) noeth

  bfs : GraphOf A → A → Stream (List A)
  bfs g = tabulate ∘ flip (ids g)
