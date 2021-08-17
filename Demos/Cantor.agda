{-# OPTIONS --cubical --safe #-}

module Demos.Cantor where

open import Prelude
open import Data.Bool.Properties using (false≢true; true≢false)

Stream : Type a → Type a
Stream A = ℕ → A

_∈_ : ∀ {A : Type a} (x : A) → Stream A → Type a
x ∈ xs = ∃[ i ] × (xs i ≡ x)

Countable : Type a → Type a
Countable A = Σ[ xs ⦂ Stream A ] × (∀ x → x ∈ xs)

x≢¬x : ∀ x → x ≢ not x
x≢¬x false = false≢true
x≢¬x true  = true≢false

cantor : ¬ (Countable (Stream Bool))
cantor (support , cover) =
  let p , ps = cover (λ i → not (support i i))
      q = cong (_$ p) ps
  in x≢¬x _ q
