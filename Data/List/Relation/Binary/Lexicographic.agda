{-# OPTIONS --cubical --safe #-}

open import Relation.Binary
open import Prelude hiding (Decidable)

module Data.List.Relation.Binary.Lexicographic {e ℓ₁ ℓ₂} {E : Type e} (ord : TotalOrder E ℓ₁ ℓ₂) where

open import Data.List
import Path as ≡

open TotalOrder ord renaming (refl to ≤-refl)

infix 4 _<′_ _≤′_
data _<′_ : List E → List E → Type (e ℓ⊔ ℓ₁ ℓ⊔ ℓ₂) where
  []< : ∀ {y ys}      → [] <′ y ∷ ys
  <∷< : ∀ {x y xs ys} → (x<y : x < y) → x ∷ xs <′ y ∷ ys
  ≡∷< : ∀ {x y xs ys} → (x≡y : x ≡ y) → (xs<ys : xs <′ ys) → x ∷ xs <′ y ∷ ys

data _≤′_ : List E → List E → Type (e ℓ⊔ ℓ₁ ℓ⊔ ℓ₂) where
  []≤ : ∀ {ys}        → [] ≤′ ys
  <∷≤ : ∀ {x y xs ys} → (x<y : x < y) → x ∷ xs ≤′ y ∷ ys
  ≡∷≤ : ∀ {x y xs ys} → (x≡y : x ≡ y) → (xs≤ys : xs ≤′ ys) → x ∷ xs ≤′ y ∷ ys

<′-trans : Transitive _<′_
<′-trans []< (<∷< x) = []<
<′-trans []< (≡∷< x y<z) = []<
<′-trans (<∷< x) (<∷< x₁) = <∷< (<-trans x x₁)
<′-trans (<∷< x) (≡∷< x₁ y<z) = <∷< (subst (_ <_) x₁ x)
<′-trans (≡∷< x x<y) (<∷< x₁) = <∷< (subst (_< _) (sym x) x₁)
<′-trans (≡∷< x x<y) (≡∷< x₁ y<z) = ≡∷< (x ; x₁) (<′-trans x<y y<z)

≤′-trans : Transitive _≤′_
≤′-trans []≤ _ = []≤
≤′-trans (<∷≤ x<y) (<∷≤ y<z) = <∷≤ (<-trans x<y y<z)
≤′-trans (<∷≤ x<y) (≡∷≤ x≡y ys≤zs) = <∷≤ (subst (_ <_) x≡y x<y)
≤′-trans (≡∷≤ x≡y xs≤ys) (<∷≤ x<y) = <∷≤ (subst (_< _) (sym x≡y) x<y)
≤′-trans (≡∷≤ x≡y xs≤ys) (≡∷≤ x≡y₁ ys≤zs) = ≡∷≤ (x≡y ; x≡y₁) (≤′-trans xs≤ys ys≤zs)

≤′-antisym : Antisymmetric _≤′_
≤′-antisym {.[]} {.[]} []≤ []≤ = ≡.refl
≤′-antisym {.(_ ∷ _)} {.(_ ∷ _)} (<∷≤ x<y) (<∷≤ x<y₁) = ⊥-elim (asym x<y x<y₁)
≤′-antisym {.(_ ∷ _)} {.(_ ∷ _)} (<∷≤ x<y) (≡∷≤ x≡y ys≤xs) = ⊥-elim (irrefl x<y (sym x≡y))
≤′-antisym {.(_ ∷ _)} {.(_ ∷ _)} (≡∷≤ x≡y xs≤ys) (<∷≤ x<y) = ⊥-elim (irrefl x<y (sym x≡y))
≤′-antisym {.(_ ∷ _)} {.(_ ∷ _)} (≡∷≤ x≡y xs≤ys) (≡∷≤ x≡y₁ ys≤xs) = cong₂ _∷_ x≡y (≤′-antisym xs≤ys ys≤xs)

≤′-refl : Reflexive _≤′_
≤′-refl {[]} = []≤
≤′-refl {x ∷ xs} = ≡∷≤ ≡.refl ≤′-refl

<′-asym : Asymmetric _<′_
<′-asym []< ()
<′-asym (<∷< x<y) (<∷< x<y₁) = asym x<y x<y₁
<′-asym (<∷< x<y) (≡∷< x≡y y<x) = irrefl x<y (sym x≡y)
<′-asym (≡∷< x≡y x<y) (<∷< x<y₁) = irrefl x<y₁ (sym x≡y)
<′-asym (≡∷< x≡y x<y) (≡∷< x≡y₁ y<x) = <′-asym x<y y<x

≮′⇒≥′ : ∀ {xs ys} → ¬ (xs <′ ys) → ys ≤′ xs
≮′⇒≥′ {xs} {[]} xs≮ys = []≤
≮′⇒≥′ {[]} {x ∷ ys} xs≮ys = ⊥-elim (xs≮ys []<)
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys with compare x y
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys | lt x<y = ⊥-elim (xs≮ys (<∷< x<y))
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys | eq x≡y = ≡∷≤ (sym x≡y) (≮′⇒≥′ (xs≮ys ∘ ≡∷< x≡y))
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys | gt x>y = <∷≤ x>y

<′-conn : Connected _<′_
<′-conn xs≮ys ys≮xs = ≤′-antisym (≮′⇒≥′ ys≮xs) (≮′⇒≥′ xs≮ys)

≰′⇒>′ : ∀ {xs ys} → ¬ (xs ≤′ ys) → ys <′ xs
≰′⇒>′ {[]} xs≰ys = ⊥-elim (xs≰ys []≤)
≰′⇒>′ {x ∷ xs} {[]} xs≰ys = []<
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys with compare x y
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | lt x<y = ⊥-elim (xs≰ys (<∷≤ x<y))
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | eq x≡y = ≡∷< (sym x≡y) (≰′⇒>′ (xs≰ys ∘ ≡∷≤ x≡y))
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | gt x>y = <∷< x>y

≮′-cons : ∀ {x y xs ys} → x ≡ y → ¬ (xs <′ ys) → ¬ (x ∷ xs <′ y ∷ ys)
≮′-cons x≡y xs≮ys (<∷< x<y) = irrefl x<y x≡y
≮′-cons x≡y xs≮ys (≡∷< x≡y₁ x∷xs<y∷ys) = xs≮ys x∷xs<y∷ys

_<′?_ : Decidable _<′_
[] <′? [] = no (λ ())
[] <′? (x ∷ ys) = yes []<
(x ∷ xs) <′? [] = no (λ ())
(x ∷ xs) <′? (y ∷ ys) with compare x y
((x ∷ xs) <′? (y ∷ ys)) | lt x<y = yes (<∷< x<y)
((x ∷ xs) <′? (y ∷ ys)) | eq x≡y = map-dec (≡∷< x≡y) (≮′-cons x≡y) (xs <′? ys)
((x ∷ xs) <′? (y ∷ ys)) | gt x>y = no (<′-asym (<∷< x>y))

listOrd : TotalOrder (List E) _ _
StrictPartialOrder._<_ (TotalOrder.strictPartialOrder listOrd) = _<′_
StrictPartialOrder.trans (TotalOrder.strictPartialOrder listOrd) = <′-trans
StrictPartialOrder.asym (TotalOrder.strictPartialOrder listOrd) = <′-asym
StrictPartialOrder.conn (TotalOrder.strictPartialOrder listOrd) = <′-conn
PartialOrder._≤_ (TotalOrder.partialOrder listOrd) = _≤′_
PartialOrder.refl (TotalOrder.partialOrder listOrd) = ≤′-refl
PartialOrder.antisym (TotalOrder.partialOrder listOrd) = ≤′-antisym
PartialOrder.trans (TotalOrder.partialOrder listOrd) = ≤′-trans
TotalOrder._<?_ listOrd = _<′?_
TotalOrder.≰⇒> listOrd = ≰′⇒>′
TotalOrder.≮⇒≥ listOrd = ≮′⇒≥′
