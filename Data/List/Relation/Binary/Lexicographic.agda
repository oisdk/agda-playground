{-# OPTIONS --cubical --safe #-}

open import Relation.Binary
open import Prelude hiding (Decidable)

module Data.List.Relation.Binary.Lexicographic {e ℓ₁ ℓ₂} {E : Type e} (ord : TotalOrder E ℓ₁ ℓ₂) where

open import Data.List
import Path as ≡

open TotalOrder ord renaming (refl to ≤-refl)

import Data.Empty.UniversePolymorphic as Poly
import Data.Unit.UniversePolymorphic as Poly

infix 4 _<′_
_<′_ : List E → List E → Type (e ℓ⊔ ℓ₁ ℓ⊔ ℓ₂)
xs <′ []     = Poly.⊥
[] <′ y ∷ ys = Poly.⊤
x ∷ xs <′ y ∷ ys = (x < y) ⊎ ((x ≡ y) × (xs <′ ys))

infix 4 _≤′_
_≤′_ : List E → List E → Type (e ℓ⊔ ℓ₁ ℓ⊔ ℓ₂)
[]     ≤′ ys     = Poly.⊤
x ∷ xs ≤′ []     = Poly.⊥
x ∷ xs ≤′ y ∷ ys = (x < y) ⊎ ((x ≡ y) × (xs ≤′ ys))


<′-trans : Transitive _<′_
<′-trans {[]}     {y ∷ ys} {z ∷ zs} p q = Poly.tt
<′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inl p) (inl q) = inl (<-trans p q)
<′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inl p) (inr q) = inl (subst (_ <_) (fst q) p)
<′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inr p) (inl q) = inl (subst (_< _) (sym (fst p)) q)
<′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inr (p , ps)) (inr (q , qs)) = inr (p ; q , <′-trans ps qs)

≤′-trans : Transitive _≤′_
≤′-trans {[]} {ys} {zs} p q = Poly.tt
≤′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inl p) (inl q) = inl (<-trans p q)
≤′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inl p) (inr q) = inl (subst (_ <_) (fst q) p)
≤′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inr p) (inl q) = inl (subst (_< _) (sym (fst p)) q)
≤′-trans {x ∷ xs} {y ∷ ys} {z ∷ zs} (inr (p , ps)) (inr (q , qs)) = inr (p ; q , ≤′-trans ps qs)

≤′-antisym : Antisymmetric _≤′_
≤′-antisym {[]} {[]} p q = refl
≤′-antisym {x ∷ xs} {y ∷ ys} (inl p) (inl q) = ⊥-elim (asym p q)
≤′-antisym {x ∷ xs} {y ∷ ys} (inl p) (inr q) = ⊥-elim (irrefl p (sym (fst q)))
≤′-antisym {x ∷ xs} {y ∷ ys} (inr p) (inl q) = ⊥-elim (irrefl q (sym (fst p)))
≤′-antisym {x ∷ xs} {y ∷ ys} (inr (p , ps)) (inr (_ , qs)) = cong₂ _∷_ p (≤′-antisym ps qs)

≤′-refl : Reflexive _≤′_
≤′-refl {[]} = Poly.tt
≤′-refl {x ∷ xs} = inr (refl , ≤′-refl)

<′-asym : Asymmetric _<′_
<′-asym {x ∷ xs} {y ∷ ys} (inl p) (inl q) = asym p q
<′-asym {x ∷ xs} {y ∷ ys} (inl p) (inr q) = irrefl p (sym (fst q))
<′-asym {x ∷ xs} {y ∷ ys} (inr p) (inl q) = irrefl q (sym (fst p))
<′-asym {x ∷ xs} {y ∷ ys} (inr p) (inr q) = <′-asym (snd p) (snd q)

≮′⇒≥′ : ∀ {xs ys} → ¬ (xs <′ ys) → ys ≤′ xs
≮′⇒≥′ {xs} {[]} p = Poly.tt
≮′⇒≥′ {[]} {y ∷ ys} p = ⊥-elim (p _)
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys with compare x y
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys | lt x<y = ⊥-elim (xs≮ys (inl x<y))
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys | eq x≡y = inr (sym x≡y , ≮′⇒≥′ (xs≮ys ∘ inr ∘ _,_ x≡y))
≮′⇒≥′ {x ∷ xs} {y ∷ ys} xs≮ys | gt x>y = inl x>y

<′-conn : Connected _<′_
<′-conn xs≮ys ys≮xs = ≤′-antisym (≮′⇒≥′ ys≮xs) (≮′⇒≥′ xs≮ys)

≰′⇒>′ : ∀ {xs ys} → ¬ (xs ≤′ ys) → ys <′ xs
≰′⇒>′ {[]} xs≰ys = ⊥-elim (xs≰ys _)
≰′⇒>′ {x ∷ xs} {[]} xs≰ys = Poly.tt
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys with compare x y
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | lt x<y = ⊥-elim (xs≰ys (inl x<y))
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | eq x≡y = inr (sym x≡y , ≰′⇒>′ (xs≰ys ∘ inr ∘ _,_ x≡y))
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | gt x>y = inl x>y

≮′-cons : ∀ {x y xs ys} → x ≡ y → ¬ (xs <′ ys) → ¬ (x ∷ xs <′ y ∷ ys)
≮′-cons x≡y xs≮ys (inl x<y) = irrefl x<y x≡y
≮′-cons x≡y xs≮ys (inr (x≡y₁ , x∷xs<y∷ys)) = xs≮ys x∷xs<y∷ys

_<′?_ : Decidable _<′_
xs <′? [] = no (λ ())
[] <′? (y ∷ ys) = yes Poly.tt
(x ∷ xs) <′? (y ∷ ys) with compare x y
((x ∷ xs) <′? (y ∷ ys)) | lt x<y = yes (inl x<y)
((x ∷ xs) <′? (y ∷ ys)) | eq x≡y = map-dec (inr ∘ _,_ x≡y) (≮′-cons x≡y) (xs <′? ys)
((x ∷ xs) <′? (y ∷ ys)) | gt x>y = no (<′-asym (inl x>y))

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
