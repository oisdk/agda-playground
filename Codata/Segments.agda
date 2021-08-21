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
data Colist′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
  _◃_ : ∀ w → ((w≺i : w ≺ i) → A × Colist′ A (fst w≺i)) → Colist′ A i
--              ^^^^^^^^^^^^
--              This is a proposition, by the way.

-- The monus parameter tells you how much you can inspect into the list.
Colist : Type a → Type (a ℓ⊔ ℓ)
Colist A = ∀ {i} → Colist′ A i

private
  variable
    i j : 𝑆

--------------------------------------------------------------------------------
-- Finite colists
--------------------------------------------------------------------------------

-- empty list
empty : Colist A
empty {i = i} = i ◃ λ i≺i → ⊥-elim (≺-irrefl i≺i)

_◃_∷_ : 𝑆 → A → Colist A → Colist A
(w ◃ x ∷ xs) {i} = w ◃ λ w≺i → x , xs

cons′ : ∀ w → A → Colist′ A i → Colist′ A (w ∙ i)
cons′ w x xs = w ◃ λ { (k , w∙i≡w∙k , k≢ε) → x , subst (Colist′ _) (cancelˡ w _ k w∙i≡w∙k) xs }

-- singleton
pure : A → Colist A
pure x = ε ◃ λ ε≺i → x , empty

replicate : ℕ → A → Colist A
replicate zero    x = empty
replicate (suc n) x = ε ◃ λ ε≺i → x , replicate n x

--------------------------------------------------------------------------------
-- Infinite colists
--------------------------------------------------------------------------------

module _ (B : 𝑆 → Type b) (ϕ : ∀ {i} → B i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (fst w≺i))) where
    unfold′ : Acc _≺_ i → B i → Colist′ A i
    unfold″ : Acc _≺_ i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (fst w≺i)) → Colist′ A i
    unfold‴ : Acc _≺_ i → (j≺i : j ≺ i) → j ≢ ε → B (fst j≺i) → Colist′ A (fst j≺i)

    unfold‴ (acc wf) (k , i≡j∙k , k≢ε) j≢ε xs = unfold′ (wf _ ((_ , i≡j∙k ; comm _ _ , j≢ε))) xs

    unfold″ a (w , w≢ε , xs′) = w ◃ λ w≺i → map₂ (unfold‴ a w≺i w≢ε) (xs′ w≺i)

    unfold′ a xs = unfold″ a (ϕ xs)

unfold : (fdc : WellFounded _≺_) (B : 𝑆 → Type b) (ϕ : ∀ {i} → B i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (fst w≺i))) → (∀ {i} → B i) → Colist A
unfold fdc B ϕ xs {i} = unfold′ B ϕ (fdc i) xs

-- The definition of the list lets us construct an infinite colist as long as
-- every entry uses some "fuel".
repeat : (fdc : WellFounded _≺_) (s : 𝑆) (s≢ε : s ≢ ε) (x : A) → Colist A
repeat fdc s s≢ε x = unfold fdc (const ⊤) (λ _ → s , s≢ε , const (x , tt)) tt

--------------------------------------------------------------------------------
-- Manipulating colists
--------------------------------------------------------------------------------
map : (A → B) → Colist′ A i → Colist′ B i
map f (w ◃ xs) = w ◃ λ w≺i → case xs w≺i of λ { (y , ys) → f y , map f ys }

open import Data.List using (List; _∷_; [])

take′ : ∀ i → Colist′ A i → List A
take′ i (w ◃ xs) with w <? i
... | no _ = []
... | yes w<i with xs (<⇒≺ _ _ w<i)
... | y , ys = y ∷ take′ _ ys

take : 𝑆 → Colist A → List A
take x xs = take′ x xs
