open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Segments
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

module _ (fdc : WellFounded _≺_) (B : 𝑆 → Type b) where
  module _ (ϕ : ∀ {i} → B i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (fst w≺i))) where
    unfold′ : Acc _≺_ i → B i → Stream′ A i
    unfold″ : Acc _≺_ i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (fst w≺i)) → Stream′ A i
    unfold‴ : Acc _≺_ i → (j≺i : j ≺ i) → j ≢ ε → B (fst j≺i) → Stream′ A (fst j≺i)

    unfold‴ (acc wf) (k , i≡j∙k , k≢ε) j≢ε xs = unfold′ (wf _ ((_ , i≡j∙k ; comm _ _ , j≢ε))) xs

    unfold″ a (w , w≢ε , xs′) = w ◃ λ w≺i → map₂ (unfold‴ a w≺i w≢ε) (xs′ w≺i)

    unfold′ a xs = unfold″ a (ϕ xs)

    unfold : (∀ {i} → B i) → Stream A
    unfold xs {i} = unfold′ (fdc i) xs

-- The definition of the list lets us construct an infinite colist as long as
-- every entry uses some "fuel".
module _ (fdc : WellFounded _≺_) (s : 𝑆) (s≢ε : s ≢ ε) (x : A) where
  repeat : Stream A
  repeat = unfold fdc (const ⊤) (λ _ → s , s≢ε , const (x , tt)) tt

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
