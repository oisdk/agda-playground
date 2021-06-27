{-# OPTIONS --cubical --safe --guardedness #-}

module Data.PolyP.RecursionSchemes where

open import Function hiding (_⟨_⟩_)
open import Data.Sum
open import Data.Sigma
open import Level hiding (Type) renaming (Type₀ to Type)
open import Data.Unit
open import Data.Nat
open import Data.Vec.Iterated
open import Data.Empty
open import WellFounded
open import Literals.Number
open import Data.Fin.Indexed.Literals
open import Data.Fin.Indexed.Properties
open import Data.Fin.Indexed
open import Data.Nat.Literals
open import Data.Maybe
open import Path

open import Data.PolyP.Universe

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
record <!_!> (A : Type) : Type  where
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
  []   : Layers n n
  _∷_  :  Functor (1 + m) →
          Layers n m →
          Layers n (1 + m)

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

module MapComp
    {m} {As Bs Cs : Params m}
    (f : (i : Fin m) → Bs [ i ] → Cs [ i ])
    (g : (i : Fin m) → As [ i ] → Bs [ i ])
  where
  open Mapping

  mapComp : ∀ (F : Functor n) (Fs : Layers m n) (xs : <! ⟦ F ⟧ (Fs ++∙ As) !>) →
            mapRec f F Fs [! mapRec g F Fs xs !] ≡ mapRec (λ i → f i ∘ g i) F Fs xs
  mapComp (F ⊕ G) Fs [! inl x !] = cong inl (mapComp F Fs [! x !])
  mapComp (F ⊕ G) Fs [! inr x !] = cong inr (mapComp G Fs [! x !])
  mapComp (F ⊗ G) Fs [! x , y !] = cong₂ _,_ (mapComp F Fs [! x !]) (mapComp G Fs [! y !])
  mapComp μ⟨ F ⟩  Fs [! ⟨ x ⟩ !] = cong ⟨_⟩ (mapComp F (F ∷ Fs) [! x !])
  mapComp (! i)      []       [! xs    !] = refl
  mapComp (! f0)     (F ∷ Fs) [! ⟨ x ⟩ !] = cong ⟨_⟩ (mapComp F (F ∷ Fs) [! x !])
  mapComp (! (fs i)) (F ∷ Fs) [! xs    !] = mapComp (! i) Fs [! xs !]
  mapComp ①      Fs xs = refl

map-comp : ∀ (F : Functor (suc n)) → (f : B → C) → (g : A → B) → (x : ⟦ F ⟧ (A ∷ As)) →
           map F f0 f (map F f0 g x) ≡ map F f0 (f ∘ g) x
map-comp F f g x =
  MapComp.mapComp (mapParamAt f0 f) (mapParamAt f0 g) F [] [! x !] ;
  cong (λ c → Mapping.mapRec c F [] [! x !])
    (funExt λ { f0 → refl ; (fs x) → refl } )

module MapId {m} {As : Params m}
  where
  open Mapping {m = m} {As = As} {Bs = As}

  mapId : ∀ (F : Functor n) (Fs : Layers m n) (xs : <! ⟦ F ⟧ (Fs ++∙ As) !>) →
            mapRec (λ _ x → x) F Fs xs ≡ xs .!!
  mapId (F ⊕ G) Fs [! inl x !] = cong inl (mapId F Fs [! x !])
  mapId (F ⊕ G) Fs [! inr x !] = cong inr (mapId G Fs [! x !])
  mapId (F ⊗ G) Fs [! x , y !] = cong₂ _,_ (mapId F Fs [! x !]) (mapId G Fs [! y !])
  mapId μ⟨ F ⟩  Fs [! ⟨ x ⟩ !] = cong ⟨_⟩ (mapId F (F ∷ Fs) [! x !])
  mapId (! i)      []       [! xs    !] = refl
  mapId (! f0)     (F ∷ Fs) [! ⟨ x ⟩ !] = cong ⟨_⟩ (mapId F (F ∷ Fs) [! x !])
  mapId (! (fs i)) (F ∷ Fs) [! xs    !] = mapId (! i) Fs [! xs !]
  mapId ①      Fs xs = refl

map-id : (F : Functor (suc n)) → (x : ⟦ F ⟧ (A ∷ As)) → map F f0 id x ≡ x
map-id F x =
  cong
    (λ c → Mapping.mapRec c F [] [! x !])
    (funExt (λ { f0 → refl ; (fs i) → refl})) ;
  MapId.mapId F [] [! x !]

---------------------------------------------------------------------------------
--
-- Categorical
--
---------------------------------------------------------------------------------
module Categorical (F : Functor (suc n)) (As : Params n) where
  infix 4 _≗_
  _≗_ : (A → B) → (A → B) → Set _
  f ≗ g = ∀ x → f x ≡ g x
  {-# INLINE _≗_ #-}

  Alg : Type₁
  Alg = Σ[ A ⦂ Type ] (⟦ F ⟧ (A ∷ As) → A)

  -- Hom
  _⟶_ : Alg → Alg → Type
  (A , a) ⟶ (B , b) = Σ[ h ⦂ (A → B) ] (h ∘ a ≗ b ∘ map F f0 h)

  variable
    X Y Z : Alg

  _∙_ : (Y ⟶ Z) → (X ⟶ Y) → (X ⟶ Z)
  (f ∙ g) .fst = f .fst ∘ g .fst
  _∙_ {Y = Y}  {Z = Z} {X = X} f g .snd x =
    cong (f .fst) (g .snd x) ;
    f .snd (map F f0 (g .fst) x) ;
    cong (Z .snd) (map-comp F (f .fst) (g .fst) x)


  id′ : X ⟶ X
  id′ .fst = id
  id′ {X = X} .snd x = cong (X .snd) (sym (map-id F x))

---------------------------------------------------------------------------------
--
-- Catamorphisms
--
---------------------------------------------------------------------------------


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

module _ {F : Functor (suc n)} {As : Params n} where
  cata : (⟦ F ⟧ (A ∷ As) → A) → μ F As → A
  cata alg xs = Cata.cataRec alg {Bs = As} (! f0) [] [! xs !]


module CataId {k} {F : Functor (suc k)} {As : Params k} where
  cataRecId : (G : Functor n) (Gs : Layers (suc m) n) →
              (x : <! ⟦ G ⟧ (Gs ++∙ μ F As ∷ Bs) !>) → Cata.cataRec ⟨_⟩ G Gs x ≡ !! x
  cataRecId (G₁ ⊕ G₂)  Gs       [! inl x !] = cong inl (cataRecId G₁ Gs [! x !])
  cataRecId (G₁ ⊕ G₂)  Gs       [! inr x !] = cong inr (cataRecId G₂ Gs [! x !])
  cataRecId (G₁ ⊗ G₂)  Gs       [! x , y !] = cong₂ _,_ (cataRecId G₁ Gs [! x !]) (cataRecId G₂ Gs [! y !])
  cataRecId μ⟨ G ⟩     Gs       [! ⟨ x ⟩ !] = cong ⟨_⟩ (cataRecId G (G ∷ Gs) [! x !])
  cataRecId (! f0    ) []       [! ⟨ x ⟩ !] = cong ⟨_⟩ (cataRecId F [] [! x !])
  cataRecId (! (fs i)) []       [! x     !] = refl
  cataRecId (! (fs i)) (G ∷ Gs) [! x     !] = cataRecId (! i) Gs [! x !]
  cataRecId (! f0    ) (G ∷ Gs) [! ⟨ x ⟩ !] = cong ⟨_⟩ ( cataRecId G (G ∷ Gs) [! x !] )
  cataRecId ①          Gs       [! _     !] = refl

module _ {F : Functor (suc n)} {As : Params n} where
  cataId : (x : μ F As) → cata ⟨_⟩ x ≡ x
  cataId x = CataId.cataRecId (! f0) [] [! x !]
---------------------------------------------------------------------------------
--
-- Eliminators
--
---------------------------------------------------------------------------------

module Eliminator {As : Params k}
         {F : Functor (suc k)}
         (P : μ F As → Type)
         (f : (x : ⟦ F ⟧ (∃ P ∷ As)) → P ⟨ map F f0 fst x ⟩)
         where
  open import Path
  open Mapping
  open Cata

  alg : ⟦ F ⟧ (∃ P ∷ As) → ∃ P
  alg x = ⟨ map F f0 fst x ⟩ , f x

  mutual
    elimRec : (G : Functor n) (Gs : Layers (suc m) n) →
              (x : <! ⟦ G ⟧ (Gs ++∙ μ F As ∷ Bs) !>) →
              mapRec (mapParamAt f0 fst) G Gs [! cataRec alg G Gs x !] ≡ !! x
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
  elim x = subst P (elimRec {Bs = As} (! f0) [] [! x !]) (snd (cata alg x))

module _ {F : Functor (suc n)} where
  elim : (P : μ F As → Type) →
         ((x : ⟦ F ⟧ (∃ P ∷ As)) → P ⟨ map F f0 fst x ⟩) →
         (x : μ F As) → P x
  elim = Eliminator.elim

module AlgIsomorphism {F : Functor (suc n)} {As : Params n} where
  Alg : Type → Type
  Alg A = ⟦ F ⟧ (A ∷ As) → A

  AsAlg : Type₁
  AsAlg = ∀ A → Alg A → A

  open import Function.Isomorphism

  toAlg : μ F As → AsAlg
  toAlg xs A alg = cata alg xs
  {-# INLINE toAlg #-}

  fromAlg : AsAlg → μ F As
  fromAlg f = f _ ⟨_⟩
  {-# INLINE fromAlg #-}


  rinv : (x : μ F As) → fromAlg (toAlg x) ≡ x
  rinv = cataId

  -- think you need parametricity for this
  -- linv : (x : AsAlg) (A : Type) (alg : Alg A) → toAlg (fromAlg x) A alg ≡ x A alg
  -- linv x A alg = {!!}

  -- isom : AsAlg ⇔ μ F As
  -- isom .fun = fromAlg
  -- isom .inv = toAlg
  -- isom .rightInv = rinv
  -- isom .leftInv x = funExt λ A → funExt λ alg → linv x A alg

---------------------------------------------------------------------------------
--
-- Anamorphisms
--
---------------------------------------------------------------------------------


-- Coinductive fixpoint
record ν (F : Functor (suc n)) (As : Params n) : Type where
  coinductive; constructor ⟪_⟫
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

module AnaInfDisplay {F : Functor (suc n)} {As : Params n} where
  ana : (A → ⟦ F ⟧ (A ∷ As)) → A → ν F As
  ana = AnaInf.ana
open AnaInfDisplay public

-- The terminating anamorphism: uses well-founded recursion to ensure we're
-- building a finite type.
module AnaTerm {B : Type} {_<_ : B → B → Type} (<-wellFounded : WellFounded _<_)
         {k} {F : Functor (suc k)}
         {As : Params k}
         (coalg : (x : B) → ⟦ F ⟧ (∃ (_< x)  ∷ As)) where

  pr-anaAcc : (x : B) → Acc _<_ x → μ F As
  pr-anaAcc x (acc wf) = ⟨ map F f0 (λ { (x , p) → pr-anaAcc x (wf x p) }) (coalg x)  ⟩

  pr-ana : B → μ F As
  pr-ana x = pr-anaAcc x (<-wellFounded x)

module AnaTermDisplay
  {A : Type}
  {_<_ : A → A → Type}
  {F : Functor (suc n)}
  {As : Params n}
  where
  pr-ana :  WellFounded _<_ →
            ((x : A) → ⟦ F ⟧ ((∃[ y ] (y < x)) ∷ As)) → A → μ F As
  pr-ana wf = AnaTerm.pr-ana wf

module Truncate {B : Type} {_<_ : B → B → Type} (<-wellFounded : WellFounded _<_)
                {k} {F : Functor (suc k)}
                {As : Params k} (step : (x : B) -> ⟦ F ⟧ (ν F As ∷ As) → ⟦ F ⟧ ((ν F As × ∃ (_< x)) ∷ As)) where

  truncAcc : (x : B) → Acc _<_ x → ν F As → μ F As
  truncAcc x (acc wf) xs = ⟨ map F f0 (λ { (ys , z , z<x) → truncAcc z (wf z z<x) ys}) (step x (xs .unfold)) ⟩

  trunc : B → ν F As → μ F As
  trunc x = truncAcc x (<-wellFounded x)

module TruncDisplay
  {A : Type}
  {_<_ : A → A → Type}
  {F : Functor (suc n)}
  {As : Params n} where
  trunc :  WellFounded _<_ →
           ((x : A) -> ⟦ F ⟧ (ν F As ∷ As) → ⟦ F ⟧ ((ν F As × ∃[ y ] (y < x)) ∷ As)) →
           A → ν F As → μ F As
  trunc wf step = Truncate.trunc wf step
