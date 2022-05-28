module Lambda where

open import Prelude renaming (subst to ≡-subst)
open import Data.List hiding (_!_)
open import Data.Nat.Order
open import Data.Nat.Properties

data `Type : Type where
  _`→_ : `Type → `Type → `Type
  `ℕ : `Type

infixr 7 _`→_

Context : Type
Context = List `Type

private
  variable
    Γ Δ : Context
    `A `B `C : `Type

Fin : ℕ → Type
Fin n = ∃ m × (m < n)

index : (xs : List A) → (n : ℕ) → n < length xs → A
index (x ∷ _ ) zero    _ = x
index (_ ∷ xs) (suc n) p = index xs n p


infixr 5 _∈_
record _∈_ (`A : `Type) (Γ : Context) : Type where
  constructor member
  field
    position : ℕ
    bounded : position < length Γ
    present : index Γ position bounded ≡ `A
open _∈_


infix 4 _⊢_
infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 #_
data _⊢_ (Γ : Context) : `Type → Type where
  `_ : `A ∈ Γ
      -------
     → Γ ⊢ `A

  ƛ_ : `A ∷ Γ ⊢ `B
     ---------------
     → Γ ⊢ `A `→ `B

  _·_ : Γ ⊢ `A `→ `B
      → Γ ⊢ `A
      --------------
      → Γ ⊢ `B

  `zero :
        ---------
          Γ ⊢ `ℕ

  `suc_ : Γ ⊢ `ℕ
        ---------
        → Γ ⊢ `ℕ

  case : Γ ⊢ `ℕ
       → Γ ⊢ `A
       → `ℕ ∷ Γ ⊢ `A
       ------------
       → Γ ⊢ `A

  μ_ : `A ∷ Γ ⊢ `A
     --------------
     → Γ ⊢ `A

#_ : ∀ n → {p : n < length Γ} → Γ ⊢ index Γ n p
# n = ` member n _ refl

plus : Γ ⊢ `ℕ `→ `ℕ `→ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

two : Γ ⊢ `ℕ
two = `suc `suc `zero

2+2 : Γ ⊢ `ℕ
2+2 = plus · two · two

mul : Γ ⊢ `ℕ `→ `ℕ `→ `ℕ
mul = μ ƛ ƛ case (# 0) `zero (plus · # 1 · (# 3 · # 0 · # 1))

S : `A ∈ Γ → `A ∈ `B ∷ Γ
S (member i p m) = member (suc i) p m

ext : (∀ {A} → A ∈ Γ → A ∈ Δ) →
      (∀ {A B} → A ∈ B ∷ Γ → A ∈ B ∷ Δ)
ext ρ (member zero    p m) = member zero tt m
ext ρ (member (suc i) p m) = S (ρ (member i p m))

rename : (∀ {A} → A ∈ Γ → A ∈ Δ)
       → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) = ` ρ x
rename ρ (ƛ x) = ƛ rename (ext ρ) x
rename ρ (f · x) = rename ρ f · rename ρ x
rename ρ `zero = `zero
rename ρ (`suc x) = `suc rename ρ x
rename ρ (case x l r) = case (rename ρ x) (rename ρ l) (rename (ext ρ) r)
rename ρ (μ x) = μ rename (ext ρ) x

exts : (∀ {A} → A ∈ Γ → Δ ⊢ A)
     → (∀ {A B} → A ∈ B ∷ Γ → B ∷ Δ ⊢ A)
exts σ (member zero    b p) = ` member zero tt p
exts σ (member (suc i) b p) = rename S (σ (member i b p))

subst : (∀ {A} → A ∈ Γ → Δ ⊢ A)
      → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x) = σ x
subst σ (ƛ x) = ƛ subst (exts σ) x
subst σ (f · x) = subst σ f · subst σ x
subst σ `zero = `zero
subst σ (`suc x) = `suc subst σ x
subst σ (case x l r) = case (subst σ x) (subst σ l) (subst (exts σ) r)
subst σ (μ x) = μ subst (exts σ) x

_[_] : `B ∷ Γ ⊢ `A
     → Γ ⊢ `B
     --------
     → Γ ⊢ `A
N [ M ] = subst (λ { (member zero b m) → ≡-subst (_ ⊢_) m M ; (member (suc i) b m) → ` member i b m }) N

data Value : Γ ⊢ `A → Type where
  V-ƛ    : {N : `A ∷ Γ ⊢ `B} → Value (ƛ N)
  V-zero : Value (`zero {Γ})
  V-suc  : ∀ {V : Γ ⊢ `ℕ} → Value V → Value (`suc V)
