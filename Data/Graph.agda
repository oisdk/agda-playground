{-# OPTIONS --cubical --guardedness --postfix-projections #-}

module Data.Graph where

open import Prelude
open import Data.List
open import Data.Nat

-- record Thunk (A : Type a) : Type a where
--   coinductive
--   constructor ⟪_⟫
--   field force : A
-- open Thunk

-- infixr 5 _◃_
-- record Stream (A : Type a) : Type a where
--   constructor _◃_
--   coinductive
--   field
--     head : A
--     tail : (Stream A)

-- open Stream

Graph : Type a → Type a
Graph A = A → List A


Stream : Type a → Type a
Stream A = ℕ → A

pure : A → Stream A
pure x _ = x

smap : (A → B) → Stream A → Stream B
smap f xs n = f (xs n)

bfs : Graph A → A → Stream (List A)
bfs g r zero    = r ∷ []
bfs g r (suc n) = concatMap g (bfs g r n)

-- module _ {A : Type a} (g : Graph A) where
--   mutual
--     bfs-foldr : List A → Stream (List A) → Stream (List A)
--     bfs-foldr []       qs = qs
--     bfs-foldr (x ∷ xs) qs .head = x ∷ bfs-foldr xs qs .head
--     bfs-foldr (x ∷ xs) qs .tail .force = bfs-foldr (g x) (bfs-foldr xs qs .tail .force)

--     -- bfs-cons : A → Stream (List A) → Stream (List A)
--     -- bfs-cons x (q ◃ qs) = (x ∷ q) ◃ bfs-foldr (g x) qs

--   -- bfs : A → Stream (List A)
--   -- bfs r = bfs-cons r (pure [])
