{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import Algebra
open import Algebra.Monus

module Codata.Heap
  {ℓ}
  (mon : CTMAPOM ℓ)
  where

open CTMAPOM mon

open import Data.List

private variable i j : 𝑆

data Heap′ {a} (i : 𝑆) (A : Type a)  : Type (a ℓ⊔ ℓ) where
  heap : A → ∀ w → -- Segment size
          (  (w<i : w < i) → 
             List (Heap′ (i ∸ w) A)
             ) →
          Heap′ i A

Heap : Type a → Type (a ℓ⊔ ℓ)
Heap A = ∀ {i} → Heap′ i A

extract : Heap′ i A → A
extract (heap x _ _) = x

duplicate : Heap′ (i ∙ j) A → Heap′ i (Heap′ j A)
duplicate h@(heap x w xs) = heap {!!} w λ p → let q = map duplicate (subst (List ∘′ flip Heap′ _) {!!} (xs ({!!}))) in {!!}

-- --------------------------------------------------------------------------------
-- -- Empty colists
-- --------------------------------------------------------------------------------

-- -- To terminate computation you use all the fuel, making an empty list.
-- -- (I'm not sure how principled this is: semantically I don't know if I like
-- -- that the size of a segment can depend on the supplied size parameter).
-- empty : Heap A
-- empty {i = i} = i ◃ λ i<i → ⊥-elim (irrefl i<i)

-- -- --------------------------------------------------------------------------------
-- -- -- Finite derived colists
-- -- --------------------------------------------------------------------------------

-- -- -- singleton
-- -- pure : A → Heap A
-- -- pure x = x ∹ empty

-- -- replicate : ℕ → A → Heap A
-- -- replicate zero    x = empty
-- -- replicate (suc n) x = x ∹ replicate n x

-- -- --------------------------------------------------------------------------------
-- -- -- Infinite colists
-- -- --------------------------------------------------------------------------------

-- -- -- This unfold function produces an infinite list; it needs every size segment
-- -- -- be non empty so that each step uses some fuel. This is what provides the
-- -- -- termination argument.

-- -- module _
-- --     (B : 𝑆 → Type b) -- The seed type
-- --     (ϕ : ∀ {i} → -- At depth i
-- --            B i → -- With this seed
-- --            ∃ w × -- Produce a segment of size w
-- --            (w ≢ ε) × -- w can't be ε, so that we use some of the fuel to prove
-- --                      -- termination
-- --            ((w<i : w < i) → A × B (i ∸ w)) -- And produce the cons constructor.
-- --            )
-- --     -- ^ The step function
-- --     where
-- --     unfold′ : Acc _<_ i → B i → Heap′ A i
-- --     unfold′ a = uncurry _◃_
-- --               ∘ map₂
-- --                 (λ { (w≢ε , xs′) w<i →
-- --                        map₂ (case a of
-- --                               λ { (acc wf) →
-- --                                     unfold′ (wf _ (∸‿<-< _ _ w<i w≢ε)) })
-- --                             (xs′ w<i) })
-- --               ∘ ϕ

-- -- unfold : (fdc : WellFounded _<_)
-- --          (B : 𝑆 → Type b)
-- --          (ϕ : ∀ {i} → B i → ∃ w × (w ≢ ε) × ((w<i : w < i) → A × B (i ∸ w))) →
-- --          (∀ {i} → B i) → Heap A
-- -- unfold fdc B ϕ xs {i} = unfold′ B ϕ (fdc i) xs

-- -- -- Here's a simple example using the unfold function: this produces infinitely
-- -- -- repeated values, with segment size s.
-- -- repeat : (fdc : WellFounded _<_) (s : 𝑆) (s≢ε : s ≢ ε) (x : A) → Heap A
-- -- repeat fdc s s≢ε x = unfold fdc (const ⊤) (λ _ → s , s≢ε , const (x , tt)) tt

-- -- --------------------------------------------------------------------------------
-- -- -- Manipulating colists
-- -- --------------------------------------------------------------------------------

-- -- -- One important thing to note about the Heap type: it is inductive!
-- -- -- Although it does technically represent "coinduction", the constructors and
-- -- -- type itself are inductive as far as Agda can see. For that reason functions
-- -- -- like map pass the termination checker with no extra ceremony.
-- -- map : (A → B) → Heap′ A i → Heap′ B i
-- -- map f (w ◃ xs) = w ◃ λ w<i → case xs w<i of λ { (y , ys) → f y , map f ys }

-- -- -- You can extract a finite prefix of the colist.
-- -- open import Data.List using (List; _∷_; [])

-- -- take′ : ∀ i → Heap′ A i → List A
-- -- take′ i (w ◃ xs) with w <? i
-- -- ... | no _ = []
-- -- ... | yes w<i with xs w<i
-- -- ... | y , ys = y ∷ take′ _ ys

-- -- take : 𝑆 → Heap A → List A
-- -- take x xs = take′ x xs
