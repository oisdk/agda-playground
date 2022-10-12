module Graphs where

open import Prelude
open import Data.List hiding (tabulate)
open import Noetherian
open import Data.List.Membership
open import Codata.Stream

open Decidable

GraphOf : Type a → Type a
GraphOf A = A → List A

unfold¹ : (B → A × B) → A × B → Stream A
unfold¹ f (x , xs) .head = x
unfold¹ f (x , xs) .tail = unfold¹ f (f xs)

unfold : (B → A × B) → B → Stream A
unfold f = unfold¹ f ∘ f

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

  -- mutual
  --   topoSort⊙′ : List A → (List A → ∀ {seen : List A} → NoethFrom seen → B) → List A → ∀ {seen : List A} → NoethFrom seen → B
  --   topoSort⊙′ [] = id
  --   topoSort⊙′ (x ∷ xs) b = topoSort⊙ x (topoSort⊙′ xs b)

  --   topoSort⊙ : A → (List A → ∀ {seen : List A} → NoethFrom seen → B) → List A → ∀ {seen : List A} → NoethFrom seen → B
  --   topoSort⊙ x k xs nf with nf x
  --   topoSort⊙ x k xs nf | done _     = k xs nf
  --   topoSort⊙ x k xs nf | more _ nf′ = topoSort⊙′ (g x) (k ∘ _∷_ x) xs nf′
  --

module _ (noeth : Noetherian A) where
  dfs : GraphOf A → GraphOf A
  dfs g x = dfs⊙ g noeth x []

  ids : GraphOf A → ℕ → GraphOf A
  ids g n r = ids⊙ g n r (λ _ → []) noeth

  bfs : GraphOf A → A → Stream (List A)
  bfs g = tabulate ∘ flip (ids g)


-- type Graph a = a -> [a]

-- topoSort :: Ord a => Graph a -> [a] -> [a]
-- topoSort g = fst . foldr f ([], ∅)
--   where
--     f x (xs,s) 
--       | x ∈ s = (xs,s)
--       | x ∉ s = first (x:) (foldr f (xs, {x} ∪ s) (g x)) 
