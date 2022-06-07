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


variable
  M N W L V : Γ ⊢ `A

infix 2 _⟶_

data _⟶_ : Γ ⊢ `A → Γ ⊢ `A → Type where
  ξ-·₁ : L ⟶ M
       → L · N ⟶ M · N

  ξ-·₂ : Value V 
       → M ⟶ N
       ------------
       → V · M ⟶ V · N

  β-ƛ : Value  W
      → (ƛ N) · W ⟶ N [ W ]

  ξ-suc : M ⟶ N
        → `suc M ⟶ `suc N

  ξ-case : L ⟶ M
         → case L V W ⟶ case M V W

  β-zero : case `zero M N ⟶ M

  β-suc : Value V
        → case (`suc V) M N ⟶ N [ V ]

  β-μ : μ N ⟶ N [ μ N ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Type where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⟶ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- _ : plus {[]} · two · two —↠ `suc `suc `suc `suc `zero
-- _ =
--     plus · two · two
--   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--     (ƛ (ƛ case (# 1) (# 0) (`suc {!plus · {!!} · {!!}!}) )) · two · two
--   —→⟨ {!!} ⟩
--   -- —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   --   (ƛ case two (` member 0 tt refl) (`suc (plus · ` member 0 tt refl · ` member 1 tt refl))) · two
--   -- —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--   --   case two two (`suc (plus · ` member 0 tt refl · two))
--   -- —→⟨ β-suc (V-suc V-zero) ⟩
--   --   `suc (plus · `suc `zero · two)
--   -- —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   --   `suc ((ƛ ƛ case (` member 1 tt refl) (` member 0 tt refl) (`suc (plus · ` member 0 tt refl · ` member 1 tt refl)))
--   --     · `suc `zero · two)
--   -- —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--   --   `suc ((ƛ case (`suc `zero) (` member 0 tt refl) (`suc (plus · ` member 0 tt refl · ` member 1 tt refl))) · two)
--   -- —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   --   `suc (case (`suc `zero) (two) (`suc (plus · ` member 0 tt refl · two)))
--   -- —→⟨ ξ-suc (β-suc V-zero) ⟩
--   --   `suc (`suc (plus · `zero · two))
--   -- —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   --   `suc (`suc ((ƛ ƛ case (` member 1 tt refl) (` member 0 tt refl) (`suc (plus · ` member 0 tt refl · ` member 1 tt refl)))
--   --     · `zero · two))
--   -- —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
--   --   `suc (`suc ((ƛ case `zero (` member 0 tt refl) (`suc (plus · ` member 0 tt refl · ` member 1 tt refl))) · two))
--   -- —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   --   `suc (`suc (case `zero (two) (`suc (plus · ` member 0 tt refl · two))))
--   -- —→⟨ ξ-suc (ξ-suc β-zero) ⟩
--    `suc (`suc (`suc (`suc `zero)))
--   ∎
