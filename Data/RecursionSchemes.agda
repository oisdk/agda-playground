{-# OPTIONS --cubical --safe #-}

module Data.RecursionSchemes where

open import Function
open import Data.Sum
open import Data.Sigma.Base
open import Level
open import Data.Unit
open import Data.List.Base using (List; _∷_; []; foldr; foldl)

-- The PolyP approach
data Functor : Type₀ where
  U I P : Functor
  _⊕_ _⊗_ : (F G : Functor) → Functor
  _⊚_ : (F G : Functor) → Functor

variable
  F G : Functor
  Fs : List Functor
  R S : Type₀

mutual
  ⟦_⟧ : Functor → Type₀ → Type₀ → Type₀
  ⟦ U     ⟧ A R = ⊤
  ⟦ I     ⟧ A R = R -- If these are wrapped in data types it makes the function
  ⟦ P     ⟧ A R = A -- injective, which can help with type inference.
  ⟦ F ⊕ G ⟧ A R = ⟦ F ⟧ A R ⊎ ⟦ G ⟧ A R
  ⟦ F ⊗ G ⟧ A R = ⟦ F ⟧ A R × ⟦ G ⟧ A R
  ⟦ F ⊚ G ⟧ A R = μ F (⟦ G ⟧ A R)

  record μ (F : Functor) (A : Type₀) : Type₀  where
    inductive
    constructor ⟨_⟩
    field unwrap : ⟦ F ⟧ A (μ F A)
open μ
-- We need this type to wrap the type given to some of
-- the functions on the functors.
-- This fixes those types (instead of allowing them to be
-- made by arbitrary functions), and so will allow
-- agda to determine that they're terminating.
-- i.e. without it we won't pass the termination checker.
record <!_!> (A : Type₀) : Type₀  where
  constructor [!_!]
  field value : A
open <!_!>

⟦_⊚⟧ : List (Functor × Functor) → Type₀ → Type₀
⟦_⊚⟧ = flip (foldr (λ { (F , G) A → ⟦ F ⟧ A (μ G A)}))

map′ : ∀ Fs → (A → B) → <! ⟦ Fs ⊚⟧ A !> → ⟦ Fs ⊚⟧ B
map′ []                   f [! xs     !] = f xs
map′ ((U       , F) ∷ Fs) f [! xs     !] = tt
map′ ((G₁ ⊕ G₂ , F) ∷ Fs) f [! inl x  !] = inl (map′ ((G₁ , F) ∷ Fs) f [! x !])
map′ ((G₁ ⊕ G₂ , F) ∷ Fs) f [! inr x  !] = inr (map′ ((G₂ , F) ∷ Fs) f [! x !])
map′ ((G₁ ⊗ G₂ , F) ∷ Fs) f [! x , y  !] = map′ ((G₁ , F) ∷ Fs) f [! x !] , map′ ((G₂ , F) ∷ Fs) f [! y !]
map′ ((P       , F) ∷ Fs) f [! xs     !] = map′ Fs f [! xs !]
map′ ((I       , F) ∷ Fs) f [! ⟨ xs ⟩ !] = ⟨ map′ ((F , F) ∷ Fs) f [! xs !] ⟩
map′ ((G₁ ⊚ G₂ , F) ∷ Fs) f [! ⟨ xs ⟩ !] = ⟨ map′ ((G₁ , G₁) ∷ (G₂ , F) ∷ Fs) f [! xs !] ⟩

map : (A → B) → μ F A → μ F B
map {F = F} f ⟨ xs ⟩ = ⟨ map′ ((F , F) ∷ []) f [! xs !] ⟩

⟦⊚_⟧ : List (Functor × Functor) → (Type₀ × Type₀) → (Type₀ × Type₀)
⟦⊚_⟧  = flip (foldr (λ { (G , F) (A , μA) → ⟦ F ⟧ A μA , μ G (⟦ F ⟧ A μA)}))

cata′ : ∀ G Gs → (⟦ F ⟧ A R → R) → <! uncurry ⟦ G ⟧ (⟦⊚ Gs ⟧ (A , μ F A)) !> → uncurry ⟦ G ⟧ (⟦⊚ Gs ⟧ (A , R))
cata′         (U      ) Gs               f [! _      !] = tt
cata′         (G₁ ⊕ G₂) Gs               f [! inl x  !] = inl (cata′ G₁ Gs f [! x !])
cata′         (G₁ ⊕ G₂) Gs               f [! inr x  !] = inr (cata′ G₂ Gs f [! x !])
cata′         (G₁ ⊗ G₂) Gs               f [! x , y  !] = cata′ G₁ Gs f [! x !] , cata′ G₂ Gs f [! y !]
cata′         P         []               f [! xs     !] = xs
cata′         P         ((F₁ , F₂) ∷ Fs) f [! xs     !] = cata′ F₂ Fs f [! xs !]
cata′ {F = F} I         []               f [! ⟨ xs ⟩ !] = f (cata′ F [] f [! xs !])
cata′         I         ((F₁ , F₂) ∷ Fs) f [! xs     !] = cata′ (F₁ ⊚ F₂) Fs f [! xs !]
cata′         (G₁ ⊚ G₂) Fs               f [! ⟨ xs ⟩ !] = ⟨ cata′ G₁ ((G₁ , G₂) ∷ Fs) f [! xs !] ⟩

cata : (⟦ F ⟧ A R → R) → μ F A → R
cata {F = F} f ⟨ x ⟩ = f (cata′ F [] f [! x !])

mapr : ∀ F → (R → S) → ⟦ F ⟧ A R → ⟦ F ⟧ A S
mapr U       f xs = tt
mapr I       f xs = f xs
mapr P       f xs = xs
mapr (F ⊕ G) f (inl x) = inl (mapr F f x)
mapr (F ⊕ G) f (inr x) = inr (mapr G f x)
mapr (F ⊗ G) f (x , y) = mapr F f x , mapr G f y
mapr (F ⊚ G) f x = map {F = F} (mapr G f) x

mapl : ∀ F → (A → B) → ⟦ F ⟧ A R → ⟦ F ⟧ B R
mapl U       f xs = tt
mapl I       f xs = xs
mapl P       f xs = f xs
mapl (F ⊕ G) f (inl x) = inl (mapl F f x)
mapl (F ⊕ G) f (inr x) = inr (mapl G f x)
mapl (F ⊗ G) f (x , y) = mapl F f x , mapl G f y
mapl (F ⊚ G) f x = map {F = F} (mapl G f) x

LIST : Type₀ → Type₀
LIST = μ (U ⊕ (P ⊗ I))

foldr′ : {B : Type₀} → (A → B → B) → B → LIST A → B
foldr′ f b = cata (const b ▿ uncurry f)

ROSE : Type₀ → Type₀
ROSE = μ (P ⊗ ((U ⊕ (P ⊗ I)) ⊚ I))

foldRose : (A → LIST B → B) → ROSE A → B
foldRose f = cata (uncurry f)
