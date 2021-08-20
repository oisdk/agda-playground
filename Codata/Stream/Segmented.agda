{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Stream.Segmented
  {ℓ}
  (mon : CTMAPOM ℓ)
  
  where

open CTMAPOM mon

-- This is a type for coinductive lists, with a "sized types" parameter which
-- can be an arbitrary monus.
infixr 5 _◃_
data Stream′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
  _◃_ : ∀ w → ((w≺i : w ≺ i) → A × Stream′ A (fst w≺i)) → Stream′ A i
--              ^^^^^^^^^^^^
--              This is a proposition, by the way.

-- The monus parameter tells you how much you can inspect into the stream.
-- The Stream′ A i type, then, represents a stream that's defined for a depth
-- of i; this type is a true "stream" (again, actually a colist), which is
-- defined for any depth.
Stream : Type a → Type (a ℓ⊔ ℓ)
Stream A = ∀ {i} → Stream′ A i

private
  variable
    i j : 𝑆

--------------------------------------------------------------------------------
-- Finite colists
--------------------------------------------------------------------------------

-- empty list
empty : Stream A
empty {i = i} = i ◃ λ i≺i → ⊥-elim (≺-irrefl i≺i)

_◃_∷_ : 𝑆 → A → Stream A → Stream A
(w ◃ x ∷ xs) {i} = w ◃ λ w≺i → x , xs

cons′ : ∀ w → A → Stream′ A i → Stream′ A (w ∙ i)
cons′ w x xs = w ◃ λ { (k , w∙i≡w∙k , k≢ε) → x , subst (Stream′ _) (cancelˡ w _ k w∙i≡w∙k) xs }

-- singleton
pure : A → Stream A
pure x = ε ◃ λ ε≺i → x , empty

replicate : ℕ → A → Stream A
replicate zero    x = empty
replicate (suc n) x = ε ◃ λ ε≺i → x , replicate n x

--------------------------------------------------------------------------------
-- Infinite colists
--------------------------------------------------------------------------------

-- The definition of the list lets us construct an infinite colist as long as
-- every entry uses some "fuel".
module _ (fdc : WellFounded _≺_) (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
  mutual
    repeat″ : Acc _≺_ i → (s≺i : s ≺ i) → A × Stream′ A (fst s≺i)
    repeat″ a        s≺i .fst = x
    repeat″ (acc wf) (k , i≡s∙k , k≢ε) .snd = repeat′ (wf k (s , i≡s∙k ; comm s k , s≢ε))

    repeat′ : Acc _≺_ i → Stream′ A i
    repeat′ a = s ◃ repeat″ a

  repeat : Stream A
  repeat = repeat′ (fdc _)

--------------------------------------------------------------------------------
-- Manipulating colists
--------------------------------------------------------------------------------
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
