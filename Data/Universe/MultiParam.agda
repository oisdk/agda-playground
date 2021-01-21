{-# OPTIONS --cubical #-}

module Data.Universe.MultiParam where

open import Function
open import Data.Sum
open import Data.Sigma.Base
open import Level
open import Data.Unit
open import Data.List.Base using (List; _∷_; []; foldr)
open import WellFounded
open import Data.Fin
open import Data.Nat
open import Data.Vec.Iterated
open import Data.Empty
open import Data.Maybe

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
  n m : ℕ
  F G : Functor n
  As Bs : Vec Type₀ n

record Value (A : Type₀) : Type₀ where
  constructor value
  field getValue : A
open Value

data Compose (A : Type₀) : Type₀ where
  compose : A → Compose A

mutual
  ⟦_⟧ : Functor n → Vec Type₀ n → Type₀
  ⟦ [? i ] ⟧ xs = Value (xs [ i ])
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
  map′ [? i  ] Fs f [! value xs !] = value (mapTy Fs f i [! xs !])
  map′ (F ⊕ G) Fs f [! inl x !] = inl (map′ F Fs f [! x !])
  map′ (F ⊕ G) Fs f [! inr x !] = inr (map′ G Fs f [! x !])
  map′ (F ⊗ G) Fs f [! x , y !] = map′ F Fs f [! x !] , map′ G Fs f [! y !]
  map′ (Fix F) Fs f [! ⟨ xs ⟩ !] = ⟨ map′ F (F μ∷″ Fs) f [! xs !]  ⟩
  map′ (F ⊚ G) Fs f [! compose xs !] = compose (map′ F (G ⊚∷″ Fs) f [! xs !])
  map′ 1# Fs f xs = tt

map : ((i : Fin n) → As [ i ] → Bs [ i ]) → ⟦ F ⟧ As → ⟦ F ⟧ Bs
map f x = map′ _ flat f [! x !]


-- map′ : ∀ F (Fs : Fixes n) → ⟦ F ⟧ (As) → ⟦ F ⟧ Bs
-- map′ {F = [? i ]} f (value x) = value (f i x)
-- map′ {F = F ⊕ G} f (inl x) = inl (map f x)
-- map′ {F = F ⊕ G} f (inr x) = inr (map f x)
-- map′ {F = F ⊗ G} f (x , y) = map f x , map f y
-- map′ {F = 1#   } f xs = tt
-- map′ {F = F ⊚ G} f (compose xs) = compose (map (maybe (map f) f) xs)
-- map′ {F = Fix F} f ⟨ xs ⟩ = ⟨ {!!} ⟩

-- ⟦_⊚⟧ : List (Functor × Functor) → Type₀ → Type₀
-- ⟦_⊚⟧ = flip (foldr (λ { (F , G) A → ⟦ F ⟧ A (μ G A)}))

-- map′ : ∀ Fs → (A → B) → <! ⟦ Fs ⊚⟧ A !> → ⟦ Fs ⊚⟧ B
-- map′ []                   f [! xs     !] = f xs
-- map′ ((U       , F) ∷ Fs) f [! xs     !] = tt
-- map′ ((G₁ ⊕ G₂ , F) ∷ Fs) f [! inl x  !] = inl (map′ ((G₁ , F) ∷ Fs) f [! x !])
-- map′ ((G₁ ⊕ G₂ , F) ∷ Fs) f [! inr x  !] = inr (map′ ((G₂ , F) ∷ Fs) f [! x !])
-- map′ ((G₁ ⊗ G₂ , F) ∷ Fs) f [! x , y  !] = map′ ((G₁ , F) ∷ Fs) f [! x !] , map′ ((G₂ , F) ∷ Fs) f [! y !]
-- map′ ((P       , F) ∷ Fs) f [! xs     !] = map′ Fs f [! xs !]
-- map′ ((I       , F) ∷ Fs) f [! ⟨ xs ⟩ !] = ⟨ map′ ((F , F) ∷ Fs) f [! xs !] ⟩
-- map′ ((G₁ ⊚ G₂ , F) ∷ Fs) f [! ⟨ xs ⟩ !] = ⟨ map′ ((G₁ , G₁) ∷ (G₂ , F) ∷ Fs) f [! xs !] ⟩

-- map : (A → B) → μ F A → μ F B
-- map {F = F} f ⟨ xs ⟩ = ⟨ map′ ((F , F) ∷ []) f [! xs !] ⟩

-- ⟦⊚_⟧ : List (Functor × Functor) → (Type₀ × Type₀) → (Type₀ × Type₀)
-- ⟦⊚_⟧  = flip (foldr (λ { (G , F) (A , μA) → ⟦ F ⟧ A μA , μ G (⟦ F ⟧ A μA)}))

-- cata′ : ∀ G Gs → (⟦ F ⟧ A R → R) → <! uncurry ⟦ G ⟧ (⟦⊚ Gs ⟧ (A , μ F A)) !> → uncurry ⟦ G ⟧ (⟦⊚ Gs ⟧ (A , R))
-- cata′         (U      ) Gs               f [! _      !] = tt
-- cata′         (G₁ ⊕ G₂) Gs               f [! inl x  !] = inl (cata′ G₁ Gs f [! x !])
-- cata′         (G₁ ⊕ G₂) Gs               f [! inr x  !] = inr (cata′ G₂ Gs f [! x !])
-- cata′         (G₁ ⊗ G₂) Gs               f [! x , y  !] = cata′ G₁ Gs f [! x !] , cata′ G₂ Gs f [! y !]
-- cata′         P         []               f [! xs     !] = xs
-- cata′         P         ((F₁ , F₂) ∷ Fs) f [! xs     !] = cata′ F₂ Fs f [! xs !]
-- cata′ {F = F} I         []               f [! ⟨ xs ⟩ !] = f (cata′ F [] f [! xs !])
-- cata′         I         ((F₁ , F₂) ∷ Fs) f [! xs     !] = cata′ (F₁ ⊚ F₂) Fs f [! xs !]
-- cata′         (G₁ ⊚ G₂) Fs               f [! ⟨ xs ⟩ !] = ⟨ cata′ G₁ ((G₁ , G₂) ∷ Fs) f [! xs !] ⟩

-- cata : (⟦ F ⟧ A R → R) → μ F A → R
-- cata {F = F} f ⟨ x ⟩ = f (cata′ F [] f [! x !])


-- module _ {B : Type₀} {_<_ : B → B → Type₀} (<-wellFounded : WellFounded _<_) where
--   ana′ : ∀ G Gs → ((x : B) → ⟦ F ⟧ A (∃ (_< x))) → ∀ {x} → Acc _<_ x → <! uncurry ⟦ G ⟧ (⟦⊚ Gs ⟧ (A , ∃ (_< x))) !> → uncurry ⟦ G ⟧ (⟦⊚ Gs ⟧ (A , μ F A))
--   ana′         (U      ) Gs               f a        [! _       !] = tt
--   ana′         (G₁ ⊕ G₂) Gs               f a        [! inl x   !] = inl (ana′ G₁ Gs f a [! x !])
--   ana′         (G₁ ⊕ G₂) Gs               f a        [! inr x   !] = inr (ana′ G₂ Gs f a [! x !])
--   ana′         (G₁ ⊗ G₂) Gs               f a        [! x , y   !] = ana′ G₁ Gs f a [! x !] , ana′ G₂ Gs f a [! y !]
--   ana′         P         []               f a        [! xs      !] = xs
--   ana′         P         ((F₁ , F₂) ∷ Fs) f a        [! xs      !] = ana′ F₂ Fs f a [! xs !]
--   ana′ {F = F} I         []               f (acc wf) [! y , y<x !] = ⟨ ana′ F [] f (wf y y<x) [! f y !] ⟩
--   ana′         I         ((F₁ , F₂) ∷ Fs) f a        [! xs      !] = ana′ (F₁ ⊚ F₂) Fs f a [! xs !]
--   ana′         (G₁ ⊚ G₂) Fs               f a        [! ⟨ xs  ⟩ !] = ⟨ ana′ G₁ ((G₁ , G₂) ∷ Fs) f a [! xs !] ⟩

--   ana : ((x : B) → ⟦ F ⟧ A (∃ (_< x))) → B → μ F A
--   ana {F = F} f x = ⟨ ana′ F [] f (<-wellFounded x) [! f x !] ⟩

-- mapr : ∀ F → (R → S) → ⟦ F ⟧ A R → ⟦ F ⟧ A S
-- mapr U       f xs = tt
-- mapr I       f xs = f xs
-- mapr P       f xs = xs
-- mapr (F ⊕ G) f (inl x) = inl (mapr F f x)
-- mapr (F ⊕ G) f (inr x) = inr (mapr G f x)
-- mapr (F ⊗ G) f (x , y) = mapr F f x , mapr G f y
-- mapr (F ⊚ G) f x = map {F = F} (mapr G f) x

-- mapl : ∀ F → (A → B) → ⟦ F ⟧ A R → ⟦ F ⟧ B R
-- mapl U       f xs = tt
-- mapl I       f xs = xs
-- mapl P       f xs = f xs
-- mapl (F ⊕ G) f (inl x) = inl (mapl F f x)
-- mapl (F ⊕ G) f (inr x) = inr (mapl G f x)
-- mapl (F ⊗ G) f (x , y) = mapl F f x , mapl G f y
-- mapl (F ⊚ G) f x = map {F = F} (mapl G f) x

-- LIST : Type₀ → Type₀
-- LIST = μ (U ⊕ (P ⊗ I))

-- foldr′ : {B : Type₀} → (A → B → B) → B → LIST A → B
-- foldr′ f b = cata (const b ▿ uncurry f)

-- ROSE : Type₀ → Type₀
-- ROSE = μ (P ⊗ ((U ⊕ (P ⊗ I)) ⊚ I))

-- foldRose : (A → LIST B → B) → ROSE A → B
-- foldRose f = cata (uncurry f)

-- -- LISTLIST A = LIST (LIST A)
-- LISTLIST : Type₀ → Type₀
-- LISTLIST = μ (U ⊕ (((U ⊕ (P ⊗ I)) ⊚ P) ⊗ I))

-- pattern []′ = ⟨ inl tt ⟩
-- pattern _∷′_ x xs = ⟨ inr (x , xs) ⟩

-- levels : ROSE A → LISTLIST A
-- levels t = cata alg t []′
--   where
--   alg : A × μ (U ⊕ (P ⊗ I)) (LISTLIST A → LISTLIST A) → LISTLIST A → LISTLIST A
--   alg (x , xs) []′       = (x ∷′ []′) ∷′ foldr′ id []′ xs
--   alg (x , xs) (q ∷′ qs) = (x ∷′ q  ) ∷′ foldr′ id qs  xs


-- ROSE₂ : Type₀ → Type₀
-- ROSE₂ = COFREE ((U ⊕ (P ⊗ I)) ⊚ I)

-- -- hylo : ∀ F →
-- --        (R → ⟦ F ⟧ A R) →
-- --        (⟦ F ⟧ A S → S) →
-- --        R → S
-- -- hylo F f g = g ∘ mapr F (hylo F f g) ∘ f
