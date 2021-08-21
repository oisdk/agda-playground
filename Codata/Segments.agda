open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Segments
  {ℓ}
  (mon : CTMAPOM ℓ)
  where

open CTMAPOM mon

private variable i j : 𝑆

-- This is a type which contains some finite and some infinite lists.
-- The idea is that each entry contains a parameter (w) which says
-- how much coinductive "fuel" it uses.
-- The Colist′ A i type represents a colist which is defined down to depth
-- i; the Colist A type represents a "true" colist, i.e. a colist defined for
-- any given depth.
infixr 5 _◃_
data Colist′ {a} (A : Type a) (i : 𝑆) : Type (a ℓ⊔ ℓ) where
  _◃_ : ∀ w → ((w≺i : w ≺ i) → A × Colist′ A (i ∸ w)) → Colist′ A i
--              ^^^^^^^^^^^^                  ^^^^^^^^
--              This is a proposition         This is i ∸ w

Colist : Type a → Type (a ℓ⊔ ℓ)
Colist A = ∀ {i} → Colist′ A i

--------------------------------------------------------------------------------
-- Finite colists
--------------------------------------------------------------------------------

-- By adding a finite prefix you don't have to use any of the fuel.

_∹_ : A → Colist A → Colist A
x ∹ xs = ε ◃ λ _ → x , xs

-- To terminate computation you use all the fuel, making an empty list.
empty : Colist A
empty {i = i} = i ◃ λ i≺i → ⊥-elim (≺-irrefl i≺i)

-- singleton
pure : A → Colist A
pure x = x ∹ empty

replicate : ℕ → A → Colist A
replicate zero    x = empty
replicate (suc n) x = x ∹ replicate n x

--------------------------------------------------------------------------------
-- Infinite colists
--------------------------------------------------------------------------------

module _ (B : 𝑆 → Type b) (ϕ : ∀ {i} → B i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (i ∸ w))) where
    unfold′ : Acc _≺_ i → B i → Colist′ A i
    unfold″ : Acc _≺_ i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (i ∸ w)) → Colist′ A i
    unfold‴ : Acc _≺_ i → (j≺i : j ≺ i) → j ≢ ε → B (i ∸ j) → Colist′ A (i ∸ j)

    unfold‴ (acc wf) (k , i≡j∙k , k≢ε) j≢ε xs = unfold′ (wf _ (_ , sym (≤‿∸‿cancel _ _ (k , i≡j∙k)) , j≢ε)) xs

    unfold″ a (w , w≢ε , xs′) = w ◃ λ w≺i → map₂ (unfold‴ a w≺i w≢ε) (xs′ w≺i)

    unfold′ a xs = unfold″ a (ϕ xs)

unfold : (fdc : WellFounded _≺_) (B : 𝑆 → Type b) (ϕ : ∀ {i} → B i → ∃ w × (w ≢ ε) × ((w≺i : w ≺ i) → A × B (i ∸ w))) → (∀ {i} → B i) → Colist A
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
