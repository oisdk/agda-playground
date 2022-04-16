{-# OPTIONS --no-termination-check #-}

module Hyper.Monadic.Example where

open import Prelude
open import Data.Maybe
open import Data.Maybe.Properties

open import Hyper.Monadic {𝑀 = Maybe} (maybeMonad {a = ℓzero})

open import Data.List
infixr 6 _&_
record Tree (A : Type a) : Type a where
  inductive; pattern
  constructor _&_
  field
    root : A
    children : List (Tree A)

open Tree

exampleTree : Tree ℕ
exampleTree
  =
    1 &
      ( 2 &
          ( 5 &
              ( 9  & []
              ∷ 10 & []
              ∷ [])
          ∷ 6 & []
          ∷ [])
      ∷ 3 & []
      ∷ 4 &
          ( 7 &
              ( 11 & []
              ∷ 12 & []
              ∷ [])
          ∷ 8 & []
          ∷ [])
      ∷ [])

run⟨_⟩ : A → A ↬ A → A
run⟨ b ⟩ x = x · maybe b run⟨ b ⟩

𝔼 : A ↬ A
𝔼 · k = k nothing

𝕃 : A ↬′ A → A ↬ A
𝕃 x · k = x (just (𝕃 k))

𝔽 : Maybe (A ↬ A) → A ↬ A
𝔽 = maybe 𝔼 id

module _ {A : Type} where
  bfs : Tree A → List A
  bfs t = run⟨ [] ⟩ (f t 𝔼)
    where
    f : Tree A → (List A ↬ List A) → (List A ↬ List A)
    f (t & ts) fw · bw = t ∷ (fw · bw ∘ just ∘ flip (foldr f) ts ∘ 𝔽)

_ : bfs exampleTree ≡ (1 ⋯ 12)
_ = refl
