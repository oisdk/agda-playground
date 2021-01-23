{-# OPTIONS --cubical --safe #-}

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
  𝟘 𝟙 : Functor n                               -- ⊥ and ⊤

infixl 6 _⊕_
infixl 7 _⊗_
infixr 9 _⊚_

Params : ℕ → Type₁
Params = Vec Type₀

variable
  n m k : ℕ
  F G : Functor n
  As Bs : Params n

⇑ : Functor n → Functor (suc n)
⇑ (! x) = ! (fs x)
⇑ (x ⊕ y) = ⇑ x ⊕ ⇑ y
⇑ (x ⊗ y) = ⇑ x ⊗ ⇑ y
⇑ μ⟨ x ⟩ = μ⟨ ⇑ x ⟩
⇑ 𝟘 = 𝟘
⇑ 𝟙 = 𝟙

⇓ : Functor n → Functor (suc n)
⇓ (! x) = ! (weaken x)
⇓ (x ⊕ y) = ⇓ x ⊕ ⇓ y
⇓ (x ⊗ y) = ⇓ x ⊗ ⇓ y
⇓ μ⟨ x ⟩ = μ⟨ ⇑ x ⟩
⇓ 𝟘 = 𝟘
⇓ 𝟙 = 𝟙

paramSubst : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
paramSubst f0     f0     = nothing
paramSubst f0     (fs j) = just j
paramSubst {n = suc n} (fs i) f0     = just f0
paramSubst {n = suc n} (fs i) (fs j) = maybe nothing (just ∘ fs) (paramSubst i j)

functorSubst : Fin (suc n) → Functor n → Functor (suc n) → Functor n
functorSubst i xs (! j) = maybe xs ! (paramSubst i j)
functorSubst i xs (ys ⊕ zs) = functorSubst i xs ys ⊕ functorSubst i xs zs
functorSubst i xs (ys ⊗ zs) = functorSubst i xs ys ⊗ functorSubst i xs zs
functorSubst i xs μ⟨ ys ⟩ = μ⟨ functorSubst (fs i) (⇑ xs) ys ⟩
functorSubst i xs 𝟘 = 𝟘
functorSubst i xs 𝟙 = 𝟙

_⊚_ : Functor (suc n) → Functor n → Functor n
xs ⊚ ys = functorSubst 0 ys xs

mutual
  ⟦_⟧ : Functor n → Params n → Type₀
  ⟦ ! i ⟧ xs = xs [ i ]
  ⟦ F ⊕ G ⟧ xs = ⟦ F ⟧ xs ⊎ ⟦ G ⟧ xs
  ⟦ F ⊗ G ⟧ xs = ⟦ F ⟧ xs × ⟦ G ⟧ xs
  ⟦ μ⟨ F ⟩ ⟧ xs = μ F xs
  ⟦ 𝟘 ⟧ xs = ⊥
  ⟦ 𝟙 ⟧ xs = ⊤

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
[]      ++∙ ys = ys
(x ∷ xs) ++∙ ys = let zs = xs ++∙ ys in μ x zs ∷ zs

infixr 5 _∷_ _++∙_

module _ {m} {As Bs : Params m} (f : (i : Fin m) → As [ i ] → Bs [ i ]) where
  mutual
    mapArg : (Fs : Layers m n) →
            (j : Fin n) →
            <! Fs ++∙ As [ j ] !> → Fs ++∙ Bs [ j ]
    mapArg []      i       [! xs     !] = f i xs
    mapArg (F ∷ Fs) f0     [! ⟨ xs ⟩ !] = ⟨ mapRec F (F ∷ Fs) [! xs !] ⟩
    mapArg (F ∷ Fs) (fs i) [! xs     !] = mapArg Fs i [! xs !]

    mapRec : ∀ (F : Functor n) (Fs : Layers m n) →
            <! ⟦ F ⟧ (Fs ++∙ As) !> → ⟦ F ⟧ (Fs ++∙ Bs)
    mapRec (!   i) Fs [! xs      !] = mapArg Fs i [! xs !]
    mapRec (F ⊕ G) Fs [! inl x   !] = inl (mapRec F Fs [! x !])
    mapRec (F ⊕ G) Fs [! inr x   !] = inr (mapRec G Fs [! x !])
    mapRec (F ⊗ G) Fs [! x , y   !] = mapRec F Fs [! x !] , mapRec G Fs [! y !]
    mapRec μ⟨ F ⟩  Fs [!  ⟨ xs ⟩ !] =  ⟨ mapRec F (F ∷ Fs) [! xs !] ⟩
    mapRec 𝟙       Fs _             = tt

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
    cataArg : (Gs : Layers (suc m) n) → (i : Fin n) →
              <! Gs ++∙ μ F As ∷ Bs [ i ] !> → Gs ++∙ A ∷ Bs [ i ]
    cataArg []       f0     [! ⟨ x ⟩ !] = alg (cataRec F [] [! x !])
    cataArg []       (fs i) [! x     !] = x
    cataArg (G ∷ Gs) (fs i)  [! x     !] = cataArg Gs i [! x !]
    cataArg (G ∷ Gs) f0      [! ⟨ x ⟩ !] = ⟨ cataRec G (G ∷ Gs) [! x !] ⟩

    cataRec : (G : Functor n) (Gs : Layers (suc m) n) →
             <! ⟦ G ⟧ (Gs ++∙ μ F As ∷ Bs) !> → ⟦ G ⟧ (Gs ++∙ A ∷ Bs)
    cataRec (G₁ ⊕ G₂) Gs [! inl x   !] = inl (cataRec G₁ Gs [! x !])
    cataRec (G₁ ⊕ G₂) Gs [! inr x   !] = inr (cataRec G₂ Gs [! x !])
    cataRec (G₁ ⊗ G₂) Gs [! x , y   !] = cataRec G₁ Gs [! x !] , cataRec G₂ Gs [! y !]
    cataRec μ⟨ G ⟩    Gs [!  ⟨ xs ⟩ !] =  ⟨ cataRec G (G ∷ Gs) [! xs !] ⟩
    cataRec 𝟙         Gs [! xs      !] = tt
    cataRec (! i)     Gs [! xs      !] = cataArg Gs i [! xs !]

cata : {F : Functor (suc n)} → (⟦ F ⟧ (A ∷ As) → A) → μ F As → A
cata {As = As} alg x = cataArg alg {Bs = As} [] f0 [! x !]

module _ {As : Params k}
         {F : Functor (suc k)}
         (P : μ F As → Type₀)
         (f : (x : ⟦ F ⟧ (∃ P ∷ As)) → P ⟨ mapAt {F = F} 0 fst x ⟩)
         where
  open import Path

  alg : ⟦ F ⟧ (∃ P ∷ As) → ∃ P
  alg x = ⟨ mapAt {F = F} 0 fst x ⟩ , f x

  elimProp : μ F As → ∃ P
  elimProp = cata alg

  mutual
    elidArg : (Gs : Layers (suc m) n) → (i : Fin n) →
              (x : <! Gs ++∙ μ F As ∷ Bs [ i ] !>) →
              getty x ≡ mapArg (mapParamAt 0 fst) Gs i [! cataArg alg Gs i x !]
    elidArg []       f0     [! ⟨ x ⟩ !] = cong ⟨_⟩ (elidRec F [] [! x !])
    elidArg []       (fs i) [! x     !] = refl
    elidArg (G ∷ Gs) (fs i)  [! x     !] = elidArg Gs i [! x !]
    elidArg (G ∷ Gs) f0      [! ⟨ x ⟩ !] = cong ⟨_⟩ (elidRec G (G ∷ Gs) [! x !])

    elidRec : (G : Functor n) (Gs : Layers (suc m) n) →
              (x : <! ⟦ G ⟧ (Gs ++∙ μ F As ∷ Bs) !>) →
              getty x ≡ mapRec (mapParamAt 0 fst) G Gs [! cataRec alg G Gs x !]
    elidRec (G₁ ⊕ G₂) Gs [! inl x   !] = cong inl (elidRec G₁ Gs [! x !])
    elidRec (G₁ ⊕ G₂) Gs [! inr x   !] = cong inr (elidRec G₂ Gs [! x !])
    elidRec (G₁ ⊗ G₂) Gs [! x , y   !] = cong₂ _,_ (elidRec G₁ Gs [! x !]) (elidRec G₂ Gs [! y !])
    elidRec μ⟨ G ⟩    Gs [!  ⟨ xs ⟩ !] = cong ⟨_⟩  (elidRec G (G ∷ Gs) [! xs !])
    elidRec 𝟙         Gs [! tt      !] = refl
    elidRec (! i)     Gs [!   xs    !] = elidArg Gs i [! xs !]

  elimId : ∀ x → x ≡ fst (elimProp x)
  elimId x = elidArg {Bs = As} [] 0 [! x !]

  elim : ∀ x → P x
  elim x = subst P (sym (elimId x)) (snd (elimProp x))

module _ {B : Type₀} {_<_ : B → B → Type₀} (<-wellFounded : WellFounded _<_)
         {k} {F : Functor (suc k)}
         {As : Params k}
         (coalg : (x : B) → ⟦ F ⟧ (∃ (_< x)  ∷ As)) where

  anaAcc : (x : B) → Acc _<_ x → μ F As
  anaAcc x (acc wf) = ⟨ mapAt {F = F} 0 (λ { (x , p) → anaAcc x (wf x p) }) (coalg x)  ⟩

  ana : B → μ F As
  ana x = anaAcc x (<-wellFounded x)

Curriedⁿ : ℕ → Type₁
Curriedⁿ zero    = Type₀
Curriedⁿ (suc n) = Type₀ → Curriedⁿ n

Curryⁿ : ∀ n → (Params n → Type₀) → Curriedⁿ n
Curryⁿ zero    f = f []
Curryⁿ (suc n) f A = Curryⁿ n (f ∘ (A ∷_))

⟦_⟧~ : Functor n → Curriedⁿ n
⟦_⟧~ {n = n} F = Curryⁿ n ⟦ F ⟧


LIST :  Functor 1
LIST = μ⟨ 𝟙 ⊕ ! 1 ⊗ ! 0 ⟩

TREE : Functor 1
TREE = μ⟨ μ⟨ 𝟙 ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ (𝟙 ⊕ ! 1 ⊗ ! 0) ⟩

LEVELS : Functor 1
LEVELS = μ⟨ 𝟙 ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ μ⟨ 𝟙 ⊕ ! 1 ⊗ ! 0 ⟩

FREE : Functor 1 → Functor 1
FREE f = μ⟨ ! 1 ⊕ ⇑ f ⟩

FREEP : Functor 1 → Functor 1
FREEP f = μ⟨ μ⟨ 𝟙 ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ (! 1 ⊕ ⇓ f) ⟩

FREEPC : Functor 1 → Functor 1
FREEPC f = μ⟨ 𝟙 ⊕ ! 1 ⊗ ! 0 ⟩ ⊚ μ⟨ ! 1 ⊕ ⇓ f ⟩

MON : Functor 1
MON = FREEPC (! 0)


ROSE : Functor 1
ROSE = μ⟨ ! 1 ⊗ ⇑ LIST ⟩

foldr′ : {A B : Type₀} → (A → B → B) → B → ⟦ LIST ⟧~ A → B
foldr′ f b = cata (const b ▿ uncurry f)

infixr 5 _∷′_
pattern []′ = ⟨ inl tt ⟩
pattern _∷′_ x xs = ⟨ inr (x , xs) ⟩

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

