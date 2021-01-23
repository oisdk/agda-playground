{-# OPTIONS --cubical --safe --guardedness #-}

--------------------------------------------------------------------------------
--
-- A Universe for n-ary Functors
--
-- *****************************************************************************
--
-- This module defines a "universe" (in the generic programing sense) for
-- regular trees which can include multiple variables and recursion.
--
-- We also have composition, and currently we can do top-level corecursion.
--
-- This means that we have:
--
--   * Lists
--   * Recursive data types made by composition, like the free monad, or rose
--     trees.
--   * Types with one level of corecursion (like infinite lists, but not
--     infinite lists of infinite lists).
--
-- And we can do catamorphisms, anamorphisms, mapping, and dependent
-- elimination:
--
--   elim : ((x : F (∃[ y : μ F ] (P y))) → P x) → (x : μ F) → P x
--
-- For lists, this type is equivalent to:
--
--   elim : P [] -> (∀ x xs → P xs → P (x ∷ xs)) → ∀ xs → P xs
--
-- *****************************************************************************
--
-- Yet to do:
--
--   * Possibly multi-level coinductive types
--
--        Shouldn't be too difficult, but might overcomplicate the model and I
--        can't think of a place where I need multi-level coinductive type.
--
--   * Maybe a solver for isomorphisms
--
--        Likely a good bit of not-important work here, but it might be fun to
--        implement.
--
--   * Figure out the variable binding situation.
--
--        I'm quite sure my variable binding/scoping stuff here with de Bruijn
--        indices is bad and wrong: it would be worth asking someone who knows
--        about this stuff what's the normal technique.
--
--   * Make it all universe polymorphic.
--
--        I haven't spotted any place where universe polymorphism would be an
--        obstacle, so it should just slot in easily. It is tedious to add.
--
--   * Do eliminators for the anamorphism.
--
--   * Consider adding indexed types.
--------------------------------------------------------------------------------

module Data.Universe.MultiParam where

open import Function hiding (_⟨_⟩_)
open import Data.Sum
open import Data.Sigma.Base
open import Level
open import Data.Unit
open import Data.Nat
open import Data.Vec.Iterated hiding (foldr′)
open import Data.Empty
open import WellFounded
open import Literals.Number
open import Data.Fin.Indexed.Literals
open import Data.Fin.Indexed.Properties
open import Data.Fin.Indexed
open import Data.Nat.Literals
open import Data.Maybe
import Data.Maybe.Sugar as Maybe

--------------------------------------------------------------------------------
--
--  The Universe of functors we're interested in.
--
--------------------------------------------------------------------------------

data Functor (n : ℕ) : Type₀ where
  ! : Fin n → Functor n               -- Type variables (de Bruijn indexed)
  _⊕_ : (F G : Functor n) → Functor n -- Sums
  _⊗_ : (F G : Functor n) → Functor n -- Products
  μ⟨_⟩ : Functor (suc n) → Functor n  -- Inductive fixpoint
  ⓪ : Functor n                      -- ⊥
  ① : Functor n                      -- ⊤

infixl 6 _⊕_
infixl 7 _⊗_

Params : ℕ → Type₁
Params = Vec Type₀

variable
  n m k : ℕ
  F G : Functor n
  As Bs : Params n

---------------------------------------------------------------------------------
--
-- Interpretation
--
---------------------------------------------------------------------------------

mutual
  ⟦_⟧ : Functor n → Params n → Type₀
  ⟦ ! i    ⟧ xs = xs [ i ]
  ⟦ F ⊕ G  ⟧ xs = ⟦ F ⟧ xs ⊎ ⟦ G ⟧ xs
  ⟦ F ⊗ G  ⟧ xs = ⟦ F ⟧ xs × ⟦ G ⟧ xs
  ⟦ μ⟨ F ⟩ ⟧ xs = μ F xs
  ⟦ ⓪     ⟧ xs = ⊥
  ⟦ ①     ⟧ xs = ⊤

  record μ (F : Functor (suc n)) (As : Params n) : Type₀  where
    inductive
    constructor ⟨_⟩
    field unwrap : ⟦ F ⟧ (μ F As ∷ As)
open μ

-- Note:
--
--    The ⟦_⟧ function is almost injective on its first argument. If we changed
--    the first clause from
--
--        ⟦ ! i ⟧ xs = xs [ i ]
--
--    to
--
--        ⟦ ! i ⟧ xs = Value (xs [ i ])
--
--    (or something), then the typechecker would regard the function as
--    injective and type inference would work slightly better. We wouldn't have
--    to pass the Functor itself anywhere, i.e. we could call map 0 f instead of
--    map F 0 f.
--
--    However, this also means that the types defined by this interpretation
--    function have wrappers all over the place, which is a little annoying to
--    work with.

---------------------------------------------------------------------------------
--
-- Helpers for Termination
--
---------------------------------------------------------------------------------

-- This is just the identity type. We need to use it because, if --without-K is
-- turned on, Agda will only use an argument to a function to prove structural
-- descent if that argument is a concrete data type.
--
--   wont-pass : (x : Bool) → (if x then ℕ else ℕ) → ℕ
--   wont-pass false zero    = zero
--   wont-pass false (suc n) = wont-pass true n
--   wont-pass true  zero    = zero
--   wont-pass true  (suc n) = wont-pass false n
--
-- Even though we're clearly structurally descending on the second argument
-- there, Agda won't use it unless we make it concrete, like so:
--
--   will-pass : (x : Bool) → <! (if x then ℕ else ℕ) !> → ℕ
--   will-pass false [! zero  !] = zero
--   will-pass false [! suc n !] = will-pass true  [! n !]
--   will-pass true  [! zero  !] = zero
--   will-pass true  [! suc n !] = will-pass false [! n !]
record <!_!> (A : Type₀) : Type₀  where
  eta-equality
  constructor [!_!]
  field !! : A
open <!_!>

-- For the map and cata functions to be structurally
-- terminating, we can't do things like:
--
--   cata f = f ∘ fmap (cata f) ∘ unwrap
--
-- So instead we need to carry a stack of all of the functors
-- we're under at any given point, and pattern match on that to
-- tell whether we should do f or fmap f.
data Layers (n : ℕ) : ℕ → Type₁ where
  [] : Layers n n
  _∷_ : Functor (suc m) → Layers n m → Layers n (suc m)

_++∙_ : Layers n m → Params n → Params m
[]       ++∙ ys = ys
(x ∷ xs) ++∙ ys = let zs = xs ++∙ ys in μ x zs ∷ zs

infixr 5 _∷_ _++∙_

---------------------------------------------------------------------------------
--
-- Mapping
--
---------------------------------------------------------------------------------

module Mapping {m} {As Bs : Params m} (f : (i : Fin m) → As [ i ] → Bs [ i ]) where
  mapRec : ∀ (F : Functor n) (Fs : Layers m n) →
          <! ⟦ F ⟧ (Fs ++∙ As) !> → ⟦ F ⟧ (Fs ++∙ Bs)
  mapRec (F ⊕ G)    Fs       [! inl x  !] = inl (mapRec F Fs [! x !])
  mapRec (F ⊕ G)    Fs       [! inr x  !] = inr (mapRec G Fs [! x !])
  mapRec (F ⊗ G)    Fs       [! x , y  !] = mapRec F Fs [! x !] , mapRec G Fs [! y !]
  mapRec μ⟨ F ⟩     Fs       [! ⟨ xs ⟩ !] = ⟨ mapRec F (F ∷ Fs) [! xs !] ⟩
  mapRec (! i     ) []       [! xs     !] = f i xs
  mapRec (! f0    ) (F ∷ Fs) [! ⟨ xs ⟩ !] = ⟨ mapRec F (F ∷ Fs) [! xs !] ⟩
  mapRec (! (fs i)) (F ∷ Fs) [! xs     !] = mapRec (! i) Fs [! xs !]
  mapRec ①          Fs       _            = tt

mapParamAt : (i : Fin n) → (As [ i ] → A) → (j : Fin n) → As [ j ] → As [ i ]≔ A [ j ]
mapParamAt f0     f f0     x = f x
mapParamAt f0     f (fs _) x = x
mapParamAt (fs _) f f0     x = x
mapParamAt (fs i) f (fs j) x = mapParamAt i f j x

map : ∀ F → (i : Fin n) → (As [ i ] → A) → ⟦ F ⟧ As → ⟦ F ⟧ (As [ i ]≔ A)
map F i f xs = Mapping.mapRec (mapParamAt i f) F [] [! xs !]

---------------------------------------------------------------------------------
--
-- Catamorphisms
--
---------------------------------------------------------------------------------

open import Path

_-Alg : Functor 1 → Type₁
F -Alg = Σ[ A ⦂ Type₀ ] (⟦ F ⟧ (A ∷ []) → A)

_-Homo : (F : Functor 1) → F -Alg → F -Alg → Type₀
(F -Homo) (A , a) (B , b) = Σ[ h ⦂ (A → B) ] (h ∘ a ≡ b ∘ map F 0 h)


module Cata {k} {F : Functor (suc k)} {As : Params k} (alg : ⟦ F ⟧ (A ∷ As) → A) where
  cataRec : (G : Functor n) (Gs : Layers (suc m) n) →
            <! ⟦ G ⟧ (Gs ++∙ μ F As ∷ Bs) !> → ⟦ G ⟧ (Gs ++∙ A ∷ Bs)
  cataRec (G₁ ⊕ G₂)  Gs       [! inl x !] = inl (cataRec G₁ Gs [! x !])
  cataRec (G₁ ⊕ G₂)  Gs       [! inr x !] = inr (cataRec G₂ Gs [! x !])
  cataRec (G₁ ⊗ G₂)  Gs       [! x , y !] = cataRec G₁ Gs [! x !] , cataRec G₂ Gs [! y !]
  cataRec μ⟨ G ⟩     Gs       [! ⟨ x ⟩ !] = ⟨ cataRec G (G ∷ Gs) [! x !] ⟩
  cataRec (! f0    ) []       [! ⟨ x ⟩ !] = alg (cataRec F [] [! x !])
  cataRec (! (fs i)) []       [! x     !] = x
  cataRec (! (fs i)) (G ∷ Gs) [! x     !] = cataRec (! i) Gs [! x !]
  cataRec (! f0    ) (G ∷ Gs) [! ⟨ x ⟩ !] = ⟨ cataRec G (G ∷ Gs) [! x !] ⟩
  cataRec ①          Gs       [! _     !] = tt

  cata : μ F As → A
  cata x = cataRec {Bs = As} (! f0) [] [! x !]
open Cata using (cata)

---------------------------------------------------------------------------------
--
-- Eliminators
--
---------------------------------------------------------------------------------

module Eliminator {As : Params k}
         {F : Functor (suc k)}
         (P : μ F As → Type₀)
         (f : (x : ⟦ F ⟧ (∃ P ∷ As)) → P ⟨ map F 0 fst x ⟩)
         where
  open import Path
  open Mapping
  open Cata

  alg : ⟦ F ⟧ (∃ P ∷ As) → ∃ P
  alg x = ⟨ map F 0 fst x ⟩ , f x

  mutual
    elimRec : (G : Functor n) (Gs : Layers (suc m) n) →
              (x : <! ⟦ G ⟧ (Gs ++∙ μ F As ∷ Bs) !>) →
              mapRec (mapParamAt 0 fst) G Gs [! cataRec alg G Gs x !] ≡ !! x
    elimRec (G₁ ⊕ G₂)   Gs       [! inl x !] = cong inl (elimRec G₁ Gs [! x !])
    elimRec (G₁ ⊕ G₂)   Gs       [! inr x !] = cong inr (elimRec G₂ Gs [! x !])
    elimRec (G₁ ⊗ G₂)   Gs       [! x , y !] = cong₂ _,_ (elimRec G₁ Gs [! x !]) (elimRec G₂ Gs [! y !])
    elimRec μ⟨ G ⟩      Gs       [! ⟨ x ⟩ !] = cong ⟨_⟩  (elimRec G (G ∷ Gs) [! x !])
    elimRec (! f0    )  []       [! ⟨ x ⟩ !] = cong ⟨_⟩ (elimRec F [] [! x !])
    elimRec (! (fs i))  []       [! x     !] = refl
    elimRec (! (fs i))  (G ∷ Gs) [! x     !] = elimRec (! i) Gs [! x !]
    elimRec (! f0    )  (G ∷ Gs) [! ⟨ x ⟩ !] = cong ⟨_⟩ (elimRec G (G ∷ Gs) [! x !])
    elimRec ①          Gs        [! _     !] = refl

  elim : ∀ x → P x
  elim x = subst P (elimRec {Bs = As} (! 0) [] [! x !]) (snd (cata alg x))
open Eliminator using (elim) public

---------------------------------------------------------------------------------
--
-- Anamorphisms
--
---------------------------------------------------------------------------------


-- Coinductive fixpoint
record ν (F : Functor (suc n)) (As : Params n) : Type₀ where
  coinductive
  constructor ⟪_⟫
  field unfold : ⟦ F ⟧ (ν F As ∷ As)
open ν public

-- The "proper" anamorphism, which is coinductive.
module AnaInf {k} {F : Functor (suc k)} {As : Params k} (coalg : A → ⟦ F ⟧ (A  ∷ As)) where
  mutual
    anaRec : (G : Functor n) (Gs : Layers (suc m) n) →
             <! ⟦ G ⟧ (Gs ++∙ A ∷ Bs) !> → <! ⟦ G ⟧ (Gs ++∙ ν F As ∷ Bs) !>
    anaRec (G₁ ⊕ G₂)  Gs       [! inl x !] .!! = inl (anaRec G₁ Gs [! x !] .!!)
    anaRec (G₁ ⊕ G₂)  Gs       [! inr x !] .!! = inr (anaRec G₂ Gs [! x !] .!!)
    anaRec (G₁ ⊗ G₂)  Gs       [! x , y !] .!! .fst = anaRec G₁ Gs [! x !] .!!
    anaRec (G₁ ⊗ G₂)  Gs       [! x , y !] .!! .snd = anaRec G₂ Gs [! y !] .!!
    anaRec μ⟨ G ⟩     Gs       [! ⟨ x ⟩ !] .!! = ⟨ anaRec G (G ∷ Gs) [! x !] .!! ⟩
    anaRec (! f0    ) []       [! x     !] .!! = ana x
    anaRec (! (fs i)) []       [! x     !] .!! = x
    anaRec (! (fs i)) (G ∷ Gs) [! x     !] .!! = anaRec (! i) Gs [! x !] .!!
    anaRec (! f0    ) (G ∷ Gs) [! ⟨ x ⟩ !] .!! = ⟨ anaRec G (G ∷ Gs) [! x !] .!! ⟩
    anaRec ①          Gs       [! _     !] .!! = tt

    ana : A → ν F As
    ana x .unfold = anaRec F [] [! coalg x !] .!!

-- The terminating anamorphism: uses well-founded recursion to ensure we're
-- building a finite type.
module AnaTerm {B : Type₀} {_<_ : B → B → Type₀} (<-wellFounded : WellFounded _<_)
         {k} {F : Functor (suc k)}
         {As : Params k}
         (coalg : (x : B) → ⟦ F ⟧ (∃ (_< x)  ∷ As)) where

  anaAcc : (x : B) → Acc _<_ x → μ F As
  anaAcc x (acc wf) = ⟨ map F 0 (λ { (x , p) → anaAcc x (wf x p) }) (coalg x)  ⟩

  ana : B → μ F As
  ana x = anaAcc x (<-wellFounded x)

module Truncate {B : Type₀} {_<_ : B → B → Type₀} (<-wellFounded : WellFounded _<_)
                {k} {F : Functor (suc k)}
                {As : Params k} (step : (x : B) -> ⟦ F ⟧ (ν F As ∷ As) → ⟦ F ⟧ ((ν F As × ∃ (_< x)) ∷ As)) where

  truncAcc : (x : B) → Acc _<_ x → ν F As → μ F As
  truncAcc x (acc wf) xs = ⟨ map F 0 (λ { (ys , z , z<x) → truncAcc z (wf z z<x) ys}) (step x (xs .unfold)) ⟩

  trunc : B → ν F As → μ F As
  trunc x = truncAcc x (<-wellFounded x)
---------------------------------------------------------------------------------
--
-- Composition
--
---------------------------------------------------------------------------------

infixr 9 _⊚_

_⇑_ : Fin (suc n) → Functor n → Functor (suc n)
i ⇑ (! j) = ! (insert i j)
i ⇑ (x ⊕ y) = i ⇑ x ⊕ i ⇑ y
i ⇑ (x ⊗ y) = i ⇑ x ⊗ i ⇑ y
i ⇑ μ⟨ x ⟩ = μ⟨ fs i ⇑ x ⟩
i ⇑ ⓪ = ⓪
i ⇑ ① = ①

⇓ : Functor n → Functor (suc n)
⇓ (! x) = ! (weaken x)
⇓ (x ⊕ y) = ⇓ x ⊕ ⇓ y
⇓ (x ⊗ y) = ⇓ x ⊗ ⇓ y
⇓ μ⟨ x ⟩ = μ⟨ f0 ⇑ x ⟩
⇓ ⓪ = ⓪
⇓ ① = ①

substAt : Fin (suc n) → Functor (suc n) → Functor n → Functor n
substAt i (! j)     xs = maybe xs ! (j \\ i)
substAt i (ys ⊕ zs) xs = substAt i ys xs ⊕ substAt i zs xs
substAt i (ys ⊗ zs) xs = substAt i ys xs ⊗ substAt i zs xs
substAt i μ⟨ ys ⟩   xs = μ⟨ substAt (fs i) ys (0 ⇑ xs) ⟩
substAt i ⓪         xs = ⓪
substAt i ①         xs = ①

_⊚_ : Functor (suc n) → Functor n → Functor n
_⊚_ = substAt 0

---------------------------------------------------------------------------------
--
-- Currying for nicer types.
--
---------------------------------------------------------------------------------

Curriedⁿ : ℕ → Type₁
Curriedⁿ zero    = Type₀
Curriedⁿ (suc n) = Type₀ → Curriedⁿ n

Curryⁿ : ∀ n → (Params n → Type₀) → Curriedⁿ n
Curryⁿ zero    f = f []
Curryⁿ (suc n) f A = Curryⁿ n (f ∘ (A ∷_))

⟦_⟧~ : Functor n → Curriedⁿ n
⟦_⟧~ {n = n} F = Curryⁿ n ⟦ F ⟧

---------------------------------------------------------------------------------
--
-- Some example types
--
---------------------------------------------------------------------------------

LIST :  Functor 1
LIST = μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩

-- The free near-semiring
TREE : Functor 1
TREE = μ⟨ μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ (① ⊕ ! 1 ⊗ ! 0) ⟩

-- Lists of lists
LEVELS : Functor 1
LEVELS = μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩

-- The free monad
FREE : Functor 1 → Functor 1
FREE f = μ⟨ ! 1 ⊕ f0 ⇑ f ⟩

ROSE : Functor 1
ROSE = μ⟨ ! 1 ⊗ f0 ⇑ LIST ⟩

foldr′ : {A B : Type₀} → (A → B → B) → B → ⟦ LIST ⟧~ A → B
foldr′ f b = cata (const b ▿ uncurry f)

infixr 5 _∷′_
pattern []′ = ⟨ inl tt ⟩
pattern _∷′_ x xs = ⟨ inr (x , xs) ⟩

_++_ : ⟦ LIST ⟧~ A → ⟦ LIST ⟧~ A → ⟦ LIST ⟧~ A
xs ++ ys = foldr′ _∷′_ ys xs

open import Data.List using (List; _∷_; [])
import Data.List as List
open import Prelude

linv : (x : ⟦ LIST ⟧~ A) → List.foldr _∷′_ []′ (foldr′ _∷_ [] x) ≡ x
linv = elim _ λ { (inl tt) → refl ; (inr (x , (xs , p))) → cong (x ∷′_) p }

rinv : (x : List A) → foldr′ _∷_ [] (List.foldr _∷′_ []′ x) ≡ x
rinv [] = refl
rinv (x ∷ xs) = cong (x ∷_) (rinv xs)

list-list : {A : Type₀} → ⟦ LIST ⟧~ A ⇔ List A
fun list-list = foldr′ _∷_ []
inv list-list = List.foldr _∷′_ []′
rightInv list-list = rinv
leftInv  list-list = linv

example : ⟦ LIST ⟧~ ℕ
example = 1 ∷′ 2 ∷′ 3 ∷′ []′
