{-# OPTIONS --cubical --safe --guardedness #-}

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

-- The universe of functors we're interested in.
-- We have
data Functor (n : ℕ) : Type₀ where
  ! : Fin n → Functor n                         -- Type variables
  _⊕_ _⊗_ : (F G : Functor n) → Functor n       -- Sums and Products
  μ⟨_⟩ : Functor (suc n) → Functor n            -- Fixpoints
  ⓪ ① : Functor n                               -- ⊥ and ⊤

infixl 6 _⊕_
infixl 7 _⊗_
infixr 9 _⊚_

Params : ℕ → Type₁
Params = Vec Type₀

variable
  n m k : ℕ
  F G : Functor n
  As Bs : Params n

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

mutual
  ⟦_⟧ : Functor n → Params n → Type₀
  ⟦ ! i ⟧ xs = xs [ i ]
  ⟦ F ⊕ G ⟧ xs = ⟦ F ⟧ xs ⊎ ⟦ G ⟧ xs
  ⟦ F ⊗ G ⟧ xs = ⟦ F ⟧ xs × ⟦ G ⟧ xs
  ⟦ μ⟨ F ⟩ ⟧ xs = μ F xs
  ⟦ ⓪ ⟧ xs = ⊥
  ⟦ ① ⟧ xs = ⊤

  record μ (F : Functor (suc n)) (As : Params n) : Type₀  where
    inductive
    constructor ⟨_⟩
    field unwrap : ⟦ F ⟧ (μ F As ∷ As)
open μ

--   * The <!_!> type makes the type of its argument concrete;
--     when it's just a type family Agda (under --without-K)
--     won't use it for termination checking.
record <!_!> (A : Type₀) : Type₀  where
  eta-equality
  constructor [!_!]
  field getty : A
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

module _ {m} {As Bs : Params m} (f : (i : Fin m) → As [ i ] → Bs [ i ]) where
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

map : ((i : Fin n) → As [ i ] → Bs [ i ]) → ⟦ F ⟧ As → ⟦ F ⟧ Bs
map {F = F} f xs = mapRec f F [] [! xs !]

mapParamAt : (i : Fin n) → (As [ i ] → A) → (j : Fin n) → As [ j ] → As [ i ]≔ A [ j ]
mapParamAt f0     f f0     x = f x
mapParamAt f0     f (fs _) x = x
mapParamAt (fs _) f f0     x = x
mapParamAt (fs i) f (fs j) x = mapParamAt i f j x

mapAt : (i : Fin n) → (As [ i ] → A) → ⟦ F ⟧ As → ⟦ F ⟧ (As [ i ]≔ A)
mapAt {F = F} i f = map {F = F} (mapParamAt i f)

module _ {k} {F : Functor (suc k)} {As : Params k} (alg : ⟦ F ⟧ (A ∷ As) → A) where
  mutual
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

cata : {F : Functor (suc n)} → (⟦ F ⟧ (A ∷ As) → A) → μ F As → A
cata {As = As} alg x = cataRec alg {Bs = As} (! f0) [] [! x !]

module Eliminator {As : Params k}
         {F : Functor (suc k)}
         (P : μ F As → Type₀)
         (f : (x : ⟦ F ⟧ (∃ P ∷ As)) → P ⟨ mapAt {F = F} 0 fst x ⟩)
         where
  open import Path

  alg : ⟦ F ⟧ (∃ P ∷ As) → ∃ P
  alg x = ⟨ mapAt {F = F} 0 fst x ⟩ , f x

  mutual
    elidRec : (G : Functor n) (Gs : Layers (suc m) n) →
              (x : <! ⟦ G ⟧ (Gs ++∙ μ F As ∷ Bs) !>) →
              mapRec (mapParamAt 0 fst) G Gs [! cataRec alg G Gs x !] ≡ getty x
    elidRec (G₁ ⊕ G₂)   Gs       [! inl x !] = cong inl (elidRec G₁ Gs [! x !])
    elidRec (G₁ ⊕ G₂)   Gs       [! inr x !] = cong inr (elidRec G₂ Gs [! x !])
    elidRec (G₁ ⊗ G₂)   Gs       [! x , y !] = cong₂ _,_ (elidRec G₁ Gs [! x !]) (elidRec G₂ Gs [! y !])
    elidRec μ⟨ G ⟩      Gs       [! ⟨ x ⟩ !] = cong ⟨_⟩  (elidRec G (G ∷ Gs) [! x !])
    elidRec (! f0    )  []       [! ⟨ x ⟩ !] = cong ⟨_⟩ (elidRec F [] [! x !])
    elidRec (! (fs i))  []       [! x     !] = refl
    elidRec (! (fs i))  (G ∷ Gs) [! x     !] = elidRec (! i) Gs [! x !]
    elidRec (! f0    )  (G ∷ Gs) [! ⟨ x ⟩ !] = cong ⟨_⟩ (elidRec G (G ∷ Gs) [! x !])
    elidRec ①          Gs        [! _     !] = refl

  elim : ∀ x → P x
  elim x = subst P (elidRec {Bs = As} (! 0) [] [! x !]) (snd (cata alg x))
open Eliminator using (elim) public

module AnaTerm {B : Type₀} {_<_ : B → B → Type₀} (<-wellFounded : WellFounded _<_)
         {k} {F : Functor (suc k)}
         {As : Params k}
         (coalg : (x : B) → ⟦ F ⟧ (∃ (_< x)  ∷ As)) where

  anaAcc : (x : B) → Acc _<_ x → μ F As
  anaAcc x (acc wf) = ⟨ mapAt {F = F} 0 (λ { (x , p) → anaAcc x (wf x p) }) (coalg x)  ⟩

  ana : B → μ F As
  ana x = anaAcc x (<-wellFounded x)

module AnaInf {k} {F : Functor (suc k)} {As : Params k} (coalg : A → ⟦ F ⟧ (A  ∷ As)) where

  record ν (F : Functor (suc n)) (As : Params n) : Type₀ where
    coinductive
    constructor ⟪_⟫
    field unfold : ⟦ F ⟧ (ν F As ∷ As)
  open ν public

  mutual
    anaRec : (G : Functor n) (Gs : Layers (suc m) n) →
             <! ⟦ G ⟧ (Gs ++∙ A ∷ Bs) !> → <! ⟦ G ⟧ (Gs ++∙ ν F As ∷ Bs) !>
    anaRec (G₁ ⊕ G₂)  Gs       [! inl x !] .getty = inl (anaRec G₁ Gs [! x !] .getty )
    anaRec (G₁ ⊕ G₂)  Gs       [! inr x !] .getty = inr (anaRec G₂ Gs [! x !] .getty )
    anaRec (G₁ ⊗ G₂)  Gs       [! x , y !] .getty .fst = anaRec G₁ Gs [! x !] .getty
    anaRec (G₁ ⊗ G₂)  Gs       [! x , y !] .getty .snd = anaRec G₂ Gs [! y !] .getty
    anaRec μ⟨ G ⟩     Gs       [! ⟨ x ⟩ !] .getty = ⟨ anaRec G (G ∷ Gs) [! x !] .getty ⟩
    anaRec (! f0    ) []       [! x     !] .getty = ana x
    anaRec (! (fs i)) []       [! x     !] .getty = x
    anaRec (! (fs i)) (G ∷ Gs) [! x     !] .getty = anaRec (! i) Gs [! x !] .getty
    anaRec (! f0    ) (G ∷ Gs) [! ⟨ x ⟩ !] .getty = ⟨ anaRec G (G ∷ Gs) [! x !] .getty ⟩
    anaRec ①          Gs       [! _     !] .getty = tt

    ana : A → ν F As
    ana x .unfold = anaRec F [] [! coalg x !] .getty


bnd : {F : Functor (suc (suc n))} → (⟦ F ⟧ (μ F (B ∷ As) ∷ μ F (B ∷ As) ∷ As) → ⟦ F ⟧ (μ F (B ∷ As) ∷ B ∷ As)) → μ F (A ∷ As) → (A → μ F (B ∷ As)) → μ F (B ∷ As)
bnd {F = F} alg xs f = cata (⟨_⟩ ∘′ alg ∘′ mapAt {F = F} 1 f) xs

Curriedⁿ : ℕ → Type₁
Curriedⁿ zero    = Type₀
Curriedⁿ (suc n) = Type₀ → Curriedⁿ n

Curryⁿ : ∀ n → (Params n → Type₀) → Curriedⁿ n
Curryⁿ zero    f = f []
Curryⁿ (suc n) f A = Curryⁿ n (f ∘ (A ∷_))

⟦_⟧~ : Functor n → Curriedⁿ n
⟦_⟧~ {n = n} F = Curryⁿ n ⟦ F ⟧

LIST :  Functor 1
LIST = μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩


TREE : Functor 1
TREE = μ⟨ μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ (① ⊕ ! 1 ⊗ ! 0) ⟩

LEVELS : Functor 1
LEVELS = μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩

FREE : Functor 1 → Functor 1
FREE f = μ⟨ ! 1 ⊕ f0 ⇑ f ⟩

FREEP : Functor 1 → Functor 1
FREEP f = μ⟨ μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ (! 1 ⊕ ⇓ f) ⟩

FREEPC : Functor 1 → Functor 1
FREEPC f = μ⟨ ① ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ μ⟨ ! 1 ⊕ ⇓ f ⟩

MON : Functor 1
MON = FREEPC (! 0)


ROSE : Functor 1
ROSE = μ⟨ ! 1 ⊗ f0 ⇑ LIST ⟩

foldr′ : {A B : Type₀} → (A → B → B) → B → ⟦ LIST ⟧~ A → B
foldr′ f b = cata (const b ▿ uncurry f)

infixr 5 _∷′_
pattern []′ = ⟨ inl tt ⟩
pattern _∷′_ x xs = ⟨ inr (x , xs) ⟩


_++_ : ⟦ LIST ⟧~ A → ⟦ LIST ⟧~ A → ⟦ LIST ⟧~ A
xs ++ ys = cata (const ys ▿ uncurry _∷′_) xs

list-bnd : ⟦ LIST ⟧~ A → (A → ⟦ LIST ⟧~ B) → ⟦ LIST ⟧~ B
list-bnd = bnd (inl ▿ (unwrap ∘′ uncurry _++_))

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

-- foldRose : (A → ⟦ LIST ⟧~ B → B) → ⟦ ROSE ⟧~ A → B
-- foldRose f = cata (λ { (x , xs) → f x xs })

example : ⟦ LIST ⟧~ ℕ
example = 1 ∷′ 2 ∷′ 3 ∷′ []′
