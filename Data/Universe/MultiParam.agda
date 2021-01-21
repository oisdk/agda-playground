{-# OPTIONS --cubical #-}

module Data.Universe.MultiParam where

open import Function
open import Data.Sum
open import Data.Sigma.Base
open import Level
open import Data.Unit
open import WellFounded
open import Data.Fin
open import Data.Nat
open import Data.Vec.Iterated
open import Data.Empty
open import Data.Maybe

open import Literals.Number
open import Data.Fin.Literals
open import Data.Nat.Literals

infixl 6 _⊕_
infixl 7 _⊗_
infixr 9 _⊚_
data Functor (n : ℕ) : Type₀ where
  [?_] : Fin n → Functor n
  _⊕_ _⊗_ : (F G : Functor n) → Functor n
  _⊚_ : Functor (suc n) → Functor n → Functor n
  Fix : Functor (suc n) → Functor n
  0# 1# : Functor n

variable
  n m k : ℕ
  F G : Functor n
  As Bs : Vec Type₀ n

data Value (A : Type₀) : Type₀ where
  value : A → Value A

data Compose (A : Type₀) : Type₀ where
  compose : A → Compose A

mutual
  ⟦_⟧ : Functor n → Vec Type₀ n → Type₀
  ⟦ [? i ] ⟧ xs = (xs [ i ])
  ⟦ F ⊕ G ⟧ xs = ⟦ F ⟧ xs ⊎ ⟦ G ⟧ xs
  ⟦ F ⊗ G ⟧ xs = ⟦ F ⟧ xs × ⟦ G ⟧ xs
  ⟦ F ⊚ G ⟧ xs = Compose (⟦ F ⟧ (⟦ G ⟧ xs ∷ xs))
  ⟦ Fix F ⟧ xs = μ F xs
  ⟦ 0# ⟧ xs = ⊥
  ⟦ 1# ⟧ xs = ⊤

  record μ (F : Functor (suc n)) (As : Vec Type₀ n) : Type₀  where
    inductive
    constructor ⟨_⟩
    field unwrap : ⟦ F ⟧ (μ F As ∷ As)
open μ

-- We need this type to wrap the type given to some of
-- the functions on the functors.
-- This fixes those types (instead of allowing them to be
-- made by arbitrary functions), and so will allow
-- agda to determine that they're terminating.
-- i.e. without it we won't pass the termination checker.
record <!_!> (A : Type₀) : Type₀  where
  constructor [!_!]
  field getty : A
open <!_!>

data Fixes (n : ℕ) : ℕ → Type₁ where
  flat : Fixes n n
  _⊚∷″_ : Functor m       → Fixes n m → Fixes n (suc m)
  _μ∷″_ : Functor (suc m) → Fixes n m → Fixes n (suc m)

toTypes : Fixes n m → Vec Type₀ n → Vec Type₀ m
toTypes flat      y = y
toTypes (x ⊚∷″ xs) y = let z = toTypes xs y in ⟦ x ⟧ z ∷ z
toTypes (x μ∷″ xs) y = let z = toTypes xs y in μ x z ∷ z

mutual
  mapTy : (Fs : Fixes m n) →
          ((i : Fin m) → As [ i ] → Bs [ i ]) →
          (j : Fin n) →
          <! toTypes Fs As [ j ] !> → toTypes Fs Bs [ j ]
  mapTy {n = suc n} flat       f i      [! xs !] = f i xs
  mapTy {n = suc n} (F ⊚∷″ Fs) f f0     [! xs !] = map′ F Fs f [! xs !]
  mapTy {n = suc n} (F μ∷″ Fs) f f0     [! ⟨ xs ⟩ !] = ⟨ map′ F (F μ∷″ Fs) f [! xs !] ⟩
  mapTy {n = suc n} (F ⊚∷″ Fs) f (fs i) [! xs !] = mapTy Fs f i [! xs !]
  mapTy {n = suc n} (F μ∷″ Fs) f (fs i) [! xs !] = mapTy Fs f i [! xs !]

  map′ : ∀ (F : Functor n) (Fs : Fixes m n) →
          ((i : Fin m) → As [ i ] → Bs [ i ]) →
          <! ⟦ F ⟧ (toTypes Fs As) !> → ⟦ F ⟧ (toTypes Fs Bs)
  map′ [? i  ] Fs f [! xs !] = (mapTy Fs f i [! xs !])
  map′ (F ⊕ G) Fs f [! inl x !] = inl (map′ F Fs f [! x !])
  map′ (F ⊕ G) Fs f [! inr x !] = inr (map′ G Fs f [! x !])
  map′ (F ⊗ G) Fs f [! x , y !] = map′ F Fs f [! x !] , map′ G Fs f [! y !]
  map′ (Fix F) Fs f [! ⟨ xs ⟩ !] = ⟨ map′ F (F μ∷″ Fs) f [! xs !]  ⟩
  map′ (F ⊚ G) Fs f [! compose xs !] = compose (map′ F (G ⊚∷″ Fs) f [! xs !])
  map′ 1# Fs f xs = tt

map : ((i : Fin n) → As [ i ] → Bs [ i ]) → ⟦ F ⟧ As → ⟦ F ⟧ Bs
map {F = F} f x = map′ F flat f [! x !]

mutual
  cataTy : {F : Functor (suc k)} {As : Vec Type₀ k} {Rs : Vec Type₀ m} →
           (⟦ F ⟧ (A ∷ As) → A) →
           (Gs : Fixes (suc m) n) →
           (i : Fin n) →
           <! toTypes Gs (μ F As ∷ Rs) [ i ] !> → toTypes Gs (A ∷ Rs) [ i ]
  cataTy {n = suc n} {F = F} f flat       f0     [! ⟨ x ⟩ !] = f (cata′ f F flat [! x !])
  cataTy {n = suc n} f flat       (fs i) [! x     !] = x
  cataTy {n = suc n} f (G ⊚∷″ Gs) f0     [! x     !] = cata′ f G Gs [! x !]
  cataTy {n = suc n} f (G ⊚∷″ Gs) (fs i) [! x     !] = cataTy f Gs i [! x !]
  cataTy {n = suc n} f (G μ∷″ Gs) (fs i) [! x     !] = cataTy f Gs i [! x !]
  cataTy {n = suc n} f (G μ∷″ Gs) f0     [! ⟨ x ⟩ !] = ⟨ cata′ f G (G μ∷″ Gs) [! x !] ⟩

  cata′ : ∀ {F : Functor (suc k)} {As : Vec Type₀ k} {Rs : Vec Type₀ m} →
            (⟦ F ⟧ (A ∷ As) → A) →
            (G : Functor n) (Gs : Fixes (suc m) n) →
            <! ⟦ G ⟧ (toTypes Gs (μ F As ∷ Rs)) !> → ⟦ G ⟧ (toTypes Gs (A ∷ Rs))
  cata′ f (G₁ ⊕ G₂) Gs [! inl x !] = inl (cata′ f G₁ Gs [! x !])
  cata′ f (G₁ ⊕ G₂) Gs [! inr x !] = inr (cata′ f G₂ Gs [! x !])
  cata′ f (G₁ ⊗ G₂) Gs [! x , y !] = cata′ f G₁ Gs [! x !] , cata′ f G₂ Gs [! y !]
  cata′ f (G₁ ⊚ G₂) Gs [! compose xs !] = compose (cata′ f G₁ (G₂ ⊚∷″ Gs) [! xs !])
  cata′ f (Fix G) Gs [! ⟨ xs ⟩ !] = ⟨ cata′ f G (G μ∷″ Gs) [! xs !] ⟩
  cata′ f 1# Gs [! xs !] = tt
  cata′ f [? i ] Gs [! xs !] = (cataTy f Gs i [! xs !])


cata : {F : Functor (suc n)} → (⟦ F ⟧ (A ∷ As) → A) → μ F As → A
cata {F = F} alg ⟨ x ⟩ = alg (cata′ alg F flat [! x !])


fkind : ℕ → Type₁
fkind zero    = Type₀
fkind (suc n) = Type₀ → fkind n

curried : Vec Type₀ n → Type₀ → Type₀
curried xs x = foldr′ (λ y ys → y → ys) x xs

curries : ∀ n → (Vec Type₀ n → Type₀) → fkind n
curries zero    f = f []
curries (suc n) f A = curries n (f ∘ (A ∷_))

⟦_⟧~ : Functor n → fkind n
⟦_⟧~ {n = n} F = curries n ⟦ F ⟧

LIST : Type₀ → Type₀
LIST = ⟦ Fix (1# ⊕ [? 1 ] ⊗ [? 0 ]) ⟧~

ROSE : Type₀ → Type₀
ROSE = ⟦ Fix ([? 1 ] ⊗ Fix (1# ⊕ [? 1 ] ⊗ [? 0 ])) ⟧~

foldr″ : {A B : Type₀} → (A → B → B) → B → LIST A → B
foldr″ f b = cata (const b ▿ uncurry f)

infixr 5 _∷″_
pattern []″ = ⟨ inl tt ⟩
pattern _∷″_ x xs = ⟨ inr (x , xs) ⟩


example : LIST ℕ
example = 1 ∷″ 2 ∷″ 3 ∷″ []″

-- cata : {F : Functor (suc n)} {As : Vec Type₀ n} → (⟦ F ⟧ (A ∷ As) → A) → μ F As → A
-- cata = {!!}
