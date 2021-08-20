{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Stream.Segmented
  {ℓ}
  (mon : CTMAPOM ℓ)
  (fdc : WellFounded (CTMAPOM._≺_ mon))
  where

open CTMAPOM mon

infixr 5 _◃_
data Stream′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
  _◃_ : ∀ w → ((w≺i : w ≺ i) → A × Stream′ A (fst w≺i)) → Stream′ A i

-- I think this is isomorphic to the following:
-- 
-- data Stream′ (A : Type a) : 𝑆 → Type (a ℓ⊔ ℓ) where
--   _◃_ : ∀ w {ws} → (ws ≢ ε → A × Stream′ A ws) → Stream′ A (w ∙ ws)
--
-- Which makes it seem like it should be basically this:
--
-- data Stream′ (A : Type a) : 𝑆 → Type (a ℓ⊔ ℓ) where
--   _◃_,_ : ∀ w {ws} → A → Stream′ A ws → Stream′ A (w ∙ ws)

private
  variable
    i j : 𝑆

Stream : Type a → Type (a ℓ⊔ ℓ)
Stream A = ∀ {i} → Stream′ A i

empty : Stream A
empty {i = i} = i ◃ λ i<i → ⊥-elim (≺⇒< i i i<i ≤-refl)

pure : A → Stream A
pure x {i} = ε ◃ λ ε≺i → x , empty

replicate : ℕ → A → Stream A
replicate zero    x = empty
replicate (suc n) x = ε ◃ λ ε≺i → x , replicate n x

module _ (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
  mutual
    repeat″ : Acc _≺_ i → (s≺i : s ≺ i) → A × Stream′ A (fst s≺i)
    repeat″ a        s≺i .fst = x
    repeat″ (acc wf) (k , i≡s∙k , k≢ε) .snd = repeat′ (wf k (s , i≡s∙k ; comm s k , s≢ε))

    repeat′ : Acc _≺_ i → Stream′ A i
    repeat′ a = s ◃ repeat″ a

  repeat : Stream A
  repeat = repeat′ (fdc _)

map : (A → B) → Stream′ A i → Stream′ B i
map f (w ◃ xs) = w ◃ λ w≺i → case xs w≺i of λ { (y , ys) → f y , map f ys }

open import Data.List using (List; _∷_; [])

take′ : ∀ i → Stream′ A i → List A
take′ i (w ◃ xs) with w <? i
... | no _ = []
... | yes w<i with xs (<⇒≺ _ _ w<i)
... | y , ys = y ∷ take′ _ ys

take : 𝑆 → Stream A → List A
take x xs = take′ x xs


-- module Approach1 (𝓌𝒻 : WellFounded (CTMAPOM._<_ mon)) where
--   record Stream′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
--     inductive
--     field
--       head : A
--       size : 𝑆
--       tail : (p : size ≤ i) → Maybe (Stream′ A (fst p))
--   open Stream′ public

--   private
--     variable
--       i j : 𝑆

--   Stream : Type a → Type (a ℓ⊔ ℓ)
--   Stream A = ∀ {i} → Stream′ A i

--   pure : A → Stream A
--   pure x .head = x
--   pure x .size = ε
--   pure x .tail _ = nothing

--   module _ (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
--     repeat′ : Acc _<_ i → Stream′ A i
--     repeat′ a .head = x
--     repeat′ a .size = s
--     repeat′ (acc wf) .tail (k , p) = just (repeat′ (wf _ (≤⇒≢ε⇒< k _ (s , p ; comm s k) s≢ε)))

--     repeat : Stream A
--     repeat = repeat′ (𝓌𝒻 _)

--   map : (A → B) → Stream′ A i → Stream′ B i
--   map f xs .head = f (xs .head)
--   map f xs .size = xs .size
--   map f xs .tail p = case xs .tail p of λ { nothing → nothing ; (just xs′) → just (map f xs′) }

--   open import Data.List using (List; _∷_; [])

--   take′ : ∀ i → Stream′ A i → List A
--   take′ i xs with size xs ≤? i
--   take′ i xs | no  _   = []
--   take′ i xs | yes s≤i with tail xs s≤i
--   take′ i xs | yes s≤i | nothing = []
--   take′ i xs | yes s≤i | just xs′ = head xs′ ∷ take′ _ xs′

--   take : 𝑆 → Stream A → List A
--   take x xs = head (xs {i = x}) ∷ take′ x xs
