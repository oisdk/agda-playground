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
≤′-antisym {x ∷ xs} {y ∷ ys} (inl p) (inr q) = ⊥-elim (irrefl (subst (_< _) (sym (fst q)) p))
≤′-antisym {x ∷ xs} {y ∷ ys} (inr p) (inl q) = ⊥-elim (irrefl (subst (_< _) (sym (fst p)) q))
≤′-antisym {x ∷ xs} {y ∷ ys} (inr (p , ps)) (inr (_ , qs)) = cong₂ _∷_ p (≤′-antisym ps qs)

≤′-refl : Reflexive _≤′_
≤′-refl {[]} = Poly.tt
≤′-refl {x ∷ xs} = inr (refl , ≤′-refl)

<′-asym : Asymmetric _<′_
<′-asym {x ∷ xs} {y ∷ ys} (inl p) (inl q) = asym p q
<′-asym {x ∷ xs} {y ∷ ys} (inl p) (inr q) = irrefl (subst (_< _) (sym (fst q)) p)
<′-asym {x ∷ xs} {y ∷ ys} (inr p) (inl q) = irrefl (subst (_< _) (sym (fst p)) q)
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

<′-irrefl : Irreflexive _<′_
<′-irrefl {x ∷ xs} (inl x<x) = irrefl x<x
<′-irrefl {x ∷ xs} (inr xs<xs) = <′-irrefl (snd xs<xs)

≰′⇒>′ : ∀ {xs ys} → ¬ (xs ≤′ ys) → ys <′ xs
≰′⇒>′ {[]} xs≰ys = ⊥-elim (xs≰ys _)
≰′⇒>′ {x ∷ xs} {[]} xs≰ys = Poly.tt
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys with compare x y
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | lt x<y = ⊥-elim (xs≰ys (inl x<y))
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | eq x≡y = inr (sym x≡y , ≰′⇒>′ (xs≰ys ∘ inr ∘ _,_ x≡y))
≰′⇒>′ {x ∷ xs} {y ∷ ys} xs≰ys | gt x>y = inl x>y

≮′-cons : ∀ {x y xs ys} → x ≡ y → ¬ (xs <′ ys) → ¬ (x ∷ xs <′ y ∷ ys)
≮′-cons x≡y xs≮ys (inl x<y) = irrefl (subst (_< _) x≡y x<y)
≮′-cons x≡y xs≮ys (inr (x≡y₁ , x∷xs<y∷ys)) = xs≮ys x∷xs<y∷ys

_<′?_ : Decidable _<′_
xs <′? [] = no (λ ())
[] <′? (y ∷ ys) = yes Poly.tt
(x ∷ xs) <′? (y ∷ ys) with compare x y
((x ∷ xs) <′? (y ∷ ys)) | lt x<y = yes (inl x<y)
((x ∷ xs) <′? (y ∷ ys)) | eq x≡y = map-dec (inr ∘ _,_ x≡y) (≮′-cons x≡y) (xs <′? ys)
((x ∷ xs) <′? (y ∷ ys)) | gt x>y = no (<′-asym (inl x>y))

listOrd : TotalOrder (List E) _ _
StrictPreorder._<_   (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder listOrd)) = _<′_
StrictPreorder.trans (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder listOrd)) = <′-trans
StrictPreorder.irrefl  (StrictPartialOrder.strictPreorder (TotalOrder.strictPartialOrder listOrd)) = <′-irrefl
StrictPartialOrder.conn (TotalOrder.strictPartialOrder listOrd) = <′-conn
Preorder._≤_   (PartialOrder.preorder (TotalOrder.partialOrder listOrd)) = _≤′_
Preorder.refl  (PartialOrder.preorder (TotalOrder.partialOrder listOrd)) = ≤′-refl
Preorder.trans (PartialOrder.preorder (TotalOrder.partialOrder listOrd)) = ≤′-trans
PartialOrder.antisym (TotalOrder.partialOrder listOrd) = ≤′-antisym
TotalOrder._<?_ listOrd = _<′?_
TotalOrder.≰⇒> listOrd = ≰′⇒>′
TotalOrder.≮⇒≥ listOrd = ≮′⇒≥′
