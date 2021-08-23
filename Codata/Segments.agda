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
  _◃_ : ∀ w → -- Segment size
          (  (w<i : w < i) → -- If there is enough fuel left (i is the fuel)
                             -- (also the _<_ type is a proposition)
             A × Colist′ A (i ∸ w) -- Produce an element followed by the rest of
                                   -- the list, with w taken out of the fuel.
             ) →
          Colist′ A i

Colist : Type a → Type (a ℓ⊔ ℓ)
Colist A = ∀ {i} → Colist′ A i

-- The main interesting things tyhis type can do are the following:
-- * Infinite lists.
-- * The "fuel" parameter can be an arbitrary monoid, not just ℕ
-- * Finite lists can also be specified, and the way we say something is
--   finite is by taking no fuel.
-- * Everything seems to correspond correctly to the monus axioms.

--------------------------------------------------------------------------------
-- Finite colists
--------------------------------------------------------------------------------

-- By adding a finite prefix you don't have to use any of the fuel.

_∹_ : A → Colist A → Colist A
x ∹ xs = ε ◃ λ _ → x , xs

--------------------------------------------------------------------------------
-- Empty colists
--------------------------------------------------------------------------------

-- To terminate computation you use all the fuel, making an empty list.
-- (I'm not sure how principled this is: semantically I don't know if I like
-- that the size of a segment can depend on the supplied size parameter).
empty : Colist A
empty {i = i} = i ◃ λ i<i → ⊥-elim (irrefl i<i)

--------------------------------------------------------------------------------
-- Finite derived colists
--------------------------------------------------------------------------------

-- singleton
pure : A → Colist A
pure x = x ∹ empty

replicate : ℕ → A → Colist A
replicate zero    x = empty
replicate (suc n) x = x ∹ replicate n x

--------------------------------------------------------------------------------
-- Infinite colists
--------------------------------------------------------------------------------

-- This unfold function produces an infinite list; it needs every size segment
-- be non empty so that each step uses some fuel. This is what provides the
-- termination argument.

module _
    (B : 𝑆 → Type b) -- The seed type
    (ϕ : ∀ {i} → -- At depth i
           B i → -- With this seed
           ∃ w × -- Produce a segment of size w
           (w ≢ ε) × -- w can't be ε, so that we use some of the fuel to prove
                     -- termination
           ((w<i : w < i) → A × B (i ∸ w)) -- And produce the cons constructor.
           )
    -- ^ The step function
    where
    unfold′ : Acc _<_ i → B i → Colist′ A i
    unfold′ a = uncurry _◃_
              ∘ map₂
                (λ { (w≢ε , xs′) w<i →
                       map₂ (case a of λ { (acc wf) → unfold′ (wf _ (∸‿<-< _ _ w<i w≢ε)) })
                            (xs′ w<i) })
              ∘ ϕ

unfold : (fdc : WellFounded _<_)
         (B : 𝑆 → Type b)
         (ϕ : ∀ {i} → B i → ∃ w × (w ≢ ε) × ((w<i : w < i) → A × B (i ∸ w))) →
         (∀ {i} → B i) → Colist A
unfold fdc B ϕ xs {i} = unfold′ B ϕ (fdc i) xs

-- Here's a simple example using the unfold function: this produces infinitely
-- repeated values, with segment size s.
repeat : (fdc : WellFounded _<_) (s : 𝑆) (s≢ε : s ≢ ε) (x : A) → Colist A
repeat fdc s s≢ε x = unfold fdc (const ⊤) (λ _ → s , s≢ε , const (x , tt)) tt

--------------------------------------------------------------------------------
-- Manipulating colists
--------------------------------------------------------------------------------

-- One important thing to note about the Colist type: it is inductive!
-- Although it does technically represent "coinduction", the constructors and
-- type itself are inductive as far as Agda can see. For that reason functions
-- like map pass the termination checker with no extra ceremony.
map : (A → B) → Colist′ A i → Colist′ B i
map f (w ◃ xs) = w ◃ λ w<i → case xs w<i of λ { (y , ys) → f y , map f ys }

-- You can extract a finite prefix of the colist.
open import Data.List using (List; _∷_; [])

take′ : ∀ i → Colist′ A i → List A
take′ i (w ◃ xs) with w <? i
... | no _ = []
... | yes w<i with xs w<i
... | y , ys = y ∷ take′ _ ys

take : 𝑆 → Colist A → List A
take x xs = take′ x xs
