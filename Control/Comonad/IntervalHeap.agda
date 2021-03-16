{-# OPTIONS --cubical --safe --postfix-projections --guardedness #-}

open import Algebra
open import Prelude
import Algebra.Construct.OrderedMonoid as OrdMon
open import Relation.Binary
open import WellFounded
open import Algebra.Monus

module Control.Comonad.IntervalHeap {s} (mon : Monus s) (wf : WellFounded (Monus._<_ mon)) where

open Monus mon

record Heap {a} (A : Type a) : Type (s ℓ⊔ a) where
  coinductive
  constructor node
  field
    weight : 𝑆
    weight≢0 : weight ≢ ε
    val : A
    tail : Heap A
open Heap public

-- Func : Type a → Type _
-- Func A = 𝑆 → ∃[ w ] (w ≢ ε) × A

-- toFunc′ : Heap A → (w : 𝑆) → Acc _<_ w → ∃[ w ] (w ≢ ε) × A
-- toFunc′ xs w r with compare w (weight xs)
-- toFunc′ xs w r        | lt d = {!!} -- d , d≢0 , (val xs)
-- toFunc′ xs w (acc wf) | eq w≡w = toFunc′ (tail xs) ε (wf ε (either (⊥-elim ∘ weight≢0 xs ∘ sym w≡w ;_) id {!!}))
-- toFunc′ xs w (acc wf) | gt (d , p) = toFunc′ (tail xs) d (wf d (weight xs , weight≢0 xs , p ; comm _ _))

-- toFunc : Heap A → Func A
-- toFunc xs w = toFunc′ xs w (wf w)

-- fromFunc′ : 𝑆 → (𝑆 → ∃[ w ] (w ≢ ε) × A) → Heap A
-- fromFunc′ m f = let x , y , z = f m in λ where
--   .weight → x
--   .weight≢0 → y
--   .val → z
--   .tail → fromFunc′ (m ∙ x) f

-- fromFunc : Func A → Heap A
-- fromFunc = fromFunc′ ε

-- -- from∘to : ∀ (x : Heap A) → fromFunc (toFunc x) ≡ x
-- -- from∘to x i .weight = {!!}
-- -- from∘to x i .weight≢0 = {!!}
-- -- from∘to x i .val = {!!}
-- -- from∘to x i .tail = {!!}
