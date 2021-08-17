{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Fin.Properties where

open import Prelude
open import Data.Fin.Base
import Data.Nat.Properties as ℕ
open import Data.Nat.Properties using (+-comm)
open import Data.Nat
open import Function.Injective
open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_)

private
  variable
    n m : ℕ

suc-natfin : Σ[ m ⦂ ℕ ] × (m ℕ.< n) → Σ[ m ⦂ ℕ ] × (m ℕ.< suc n)
suc-natfin (m , p) = suc m , p

Fin-to-Nat-lt : Fin n → Σ[ m ⦂ ℕ ] × (m ℕ.< n)
Fin-to-Nat-lt {n = suc n} f0 = zero , tt
Fin-to-Nat-lt {n = suc n} (fs x) = suc-natfin (Fin-to-Nat-lt x)

Fin-from-Nat-lt : ∀ m → m ℕ.< n → Fin n
Fin-from-Nat-lt {n = suc n} zero p = f0
Fin-from-Nat-lt {n = suc n} (suc m) p = fs (Fin-from-Nat-lt m p)

Fin-Nat-lt-rightInv : ∀ m → (p : m ℕ.< n) → Fin-to-Nat-lt {n = n} (Fin-from-Nat-lt m p) ≡ (m , p)
Fin-Nat-lt-rightInv {n = suc n} zero p = refl
Fin-Nat-lt-rightInv {n = suc n} (suc m) p = cong (suc-natfin {n = n}) (Fin-Nat-lt-rightInv {n = n} m p)

Fin-Nat-lt-leftInv : (x : Fin n) → uncurry Fin-from-Nat-lt (Fin-to-Nat-lt x) ≡ x
Fin-Nat-lt-leftInv {n = suc n} f0 = refl
Fin-Nat-lt-leftInv {n = suc n} (fs x) = cong fs (Fin-Nat-lt-leftInv x)

Fin-Nat-lt : Fin n ⇔ Σ[ m ⦂ ℕ ] × (m ℕ.< n)
Fin-Nat-lt .fun = Fin-to-Nat-lt
Fin-Nat-lt .inv = uncurry Fin-from-Nat-lt
Fin-Nat-lt .rightInv = uncurry Fin-Nat-lt-rightInv
Fin-Nat-lt .leftInv = Fin-Nat-lt-leftInv

FinToℕ : Fin n → ℕ
FinToℕ {n = suc n} f0     = zero
FinToℕ {n = suc n} (fs x)  = suc (FinToℕ x)

FinToℕ-injective : ∀ {k} {m n : Fin k} → FinToℕ m ≡ FinToℕ n → m ≡ n
FinToℕ-injective {suc k} {f0}  {f0}  _ = refl
FinToℕ-injective {suc k} {f0}  {fs x} p = ⊥-elim (ℕ.znots p)
FinToℕ-injective {suc k} {fs m} {f0}  p = ⊥-elim (ℕ.snotz p)
FinToℕ-injective {suc k} {fs m} {fs x} p = cong fs (FinToℕ-injective (ℕ.injSuc p))

pred : Fin (suc n) → Fin (suc (ℕ.pred n))
pred f0 = f0
pred {n = suc n} (fs m) = m

discreteFin : ∀ {k} → Discrete (Fin k)
discreteFin {k = suc _} f0 f0 = yes refl
discreteFin {k = suc _} f0 (fs fk) = no (ℕ.znots ∘ cong FinToℕ)
discreteFin {k = suc _} (fs fj) f0 = no (ℕ.snotz ∘ cong FinToℕ)
discreteFin {k = suc _} (fs fj) (fs fk) =
  iff-dec (cong fs iff cong (λ { f0 → fk ; (fs x) → x})) (discreteFin fj fk)

isSetFin : isSet (Fin n)
isSetFin = Discrete→isSet discreteFin

FinFromℕ : (n m : ℕ) → T (n <ᵇ m) → Fin m
FinFromℕ zero (suc m) p = f0
FinFromℕ (suc n) (suc m) p = fs (FinFromℕ n m p)
