{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude hiding (_×_)

module Categories.HSets {ℓ : Level} where

open import Categories
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Data.Sigma.Properties
open import Categories.Product
open import Categories.Exponential

hSetPreCategory : PreCategory (ℓsuc ℓ) ℓ
hSetPreCategory .PreCategory.Ob = hSet _
hSetPreCategory .PreCategory.Hom (X , _) (Y , _) = X → Y
hSetPreCategory .PreCategory.Id = id
hSetPreCategory .PreCategory.Comp f g = f ∘ g
hSetPreCategory .PreCategory.assoc-Comp _ _ _ = refl
hSetPreCategory .PreCategory.Comp-Id _ = refl
hSetPreCategory .PreCategory.Id-Comp _ = refl
hSetPreCategory .PreCategory.Hom-Set {X} {Y} = isOfHLevelΠ 2 λ _ → Y .snd

open PreCategory hSetPreCategory public


_⟨×⟩_ : isSet A → isSet B → isSet (A Prelude.× B)
xs ⟨×⟩ ys = isOfHLevelΣ 2 xs (const ys)

module _ {X Y : Ob} where
  iso-iso : (X ≅ Y) ⇔ (fst X ⇔ fst Y)
  iso-iso .fun (f , g , f∘g , g∘f) = iso f g (λ x i → g∘f i x) (λ x i → f∘g i x)
  iso-iso .inv (iso f g g∘f f∘g) = f , g  , (λ i x → f∘g x i) , (λ i x → g∘f x i)
  iso-iso .rightInv _ = refl
  iso-iso .leftInv  _ = refl

  univ⇔ : (X ≡ Y) ⇔ (X ≅ Y)
  univ⇔ = equivToIso (≃ΣProp≡ (λ _ → isPropIsSet)) ⟨ trans-⇔ ⟩
          equivToIso univalence ⟨ trans-⇔ ⟩
          sym-⇔ (iso⇔equiv (snd X)) ⟨ trans-⇔ ⟩
          sym-⇔ iso-iso

hSetCategory : Category (ℓsuc ℓ) ℓ
hSetCategory .Category.preCategory = hSetPreCategory
hSetCategory .Category.univalent = isoToEquiv univ⇔

hSetProd : HasProducts hSetCategory
hSetProd .HasProducts.product X Y .Product.obj = (X .fst Prelude.× Y .fst) , X .snd ⟨×⟩ Y .snd
hSetProd .HasProducts.product X Y .Product.proj₁ = fst
hSetProd .HasProducts.product X Y .Product.proj₂ = snd
hSetProd .HasProducts.product X Y .Product.ump f g .fst z = f z , g z
hSetProd .HasProducts.product X Y .Product.ump f g .snd .fst .fst = refl
hSetProd .HasProducts.product X Y .Product.ump f g .snd .fst .snd = refl
hSetProd .HasProducts.product X Y .Product.ump f g .snd .snd (f≡ , g≡) i x = f≡ (~ i) x , g≡ (~ i) x

hSetExp : HasExponentials hSetCategory hSetProd
hSetExp  X Y .Exponential.obj = (X .fst → Y .fst) , isOfHLevelΠ 2 λ _ → Y .snd
hSetExp  X Y .Exponential.eval (f , x) = f x
hSetExp  X Y .Exponential.uniq X₁ f .fst = curry f
hSetExp  X Y .Exponential.uniq X₁ f .snd .fst = refl
hSetExp  X Y .Exponential.uniq X₁ f .snd .snd {y} x = cong curry (sym x)

open import Categories.Pullback

hSetHasPullbacks : HasPullbacks hSetCategory
hSetHasPullbacks {X = X} {Y = Y} {Z = Z} f g .Pullback.P = ∃[ ab ] (f (fst ab) ≡ g (snd ab)) , isOfHLevelΣ 2 (X .snd ⟨×⟩ Y .snd) λ xy → isProp→isSet (Z .snd (f (xy .fst)) (g (xy .snd)))
hSetHasPullbacks f g .Pullback.p₁ ((x , _) , _) = x
hSetHasPullbacks f g .Pullback.p₂ ((_ , y) , _) = y
hSetHasPullbacks f g .Pullback.commute = funExt snd
hSetHasPullbacks f g .Pullback.ump {A = A} h₁ h₂ p .fst x = (h₁ x , h₂ x) , λ i → p i x
hSetHasPullbacks f g .Pullback.ump {A = A} h₁ h₂ p .snd .fst .fst = refl
hSetHasPullbacks f g .Pullback.ump {A = A} h₁ h₂ p .snd .fst .snd = refl
hSetHasPullbacks {Z = Z} f g .Pullback.ump {A = A} h₁ h₂ p .snd .snd {i} (p₁e , p₂e) = funExt (λ x → ΣProp≡ (λ _ → Z .snd _ _) λ j → p₁e (~ j) x , p₂e (~ j) x)

hSetTerminal : Terminal
hSetTerminal .fst = Lift _ ⊤ , isProp→isSet λ _ _ → refl
hSetTerminal .snd .fst x .lower = tt
hSetTerminal .snd .snd y = funExt λ _ → refl

hSetInitial : Initial
hSetInitial .fst = Lift _ ⊥ , λ ()
hSetInitial .snd .fst ()
hSetInitial .snd .snd y i ()

open import HITs.PropositionalTruncation
open import Categories.Coequalizer

∃!′ : (A : Type a) → (A → Type b) → Type (a ℓ⊔ b)
∃!′ A P = ∥ Σ A P ∥ Prelude.× AtMostOne P

lemma23 : ∀ {p} {P : A → hProp p} → ∃!′ A (fst ∘ P) → Σ A (fst ∘ P)
lemma23 {P = P} (x , y) = rec (λ xs ys → ΣProp≡ (snd ∘ P) (y (xs .fst) (ys .fst) (xs .snd) (ys .snd))) id x

module _ {A : Type a} {P : A → Type b} (R : ∀ x → P x → hProp c) where
  uniqueChoice : (Π[ x ⦂ A ] (∃!′ (P x) (λ u → R x u .fst))) →
                 Σ[ f ⦂ Π[ x ⦂ A ] P x ] Π[ x ⦂ A ] (R x (f x) .fst)
  uniqueChoice H = fst ∘ mid , snd ∘ mid
    where
    mid : Π[ x ⦂ A ] Σ[ u ⦂ P x ] (R x u .fst)
    mid x = lemma23 {P = R x} (H x)

open import HITs.PropositionalTruncation.Sugar

module CoeqProofs {X Y : Ob} (f : X ⟶ Y) where
  KernelPair : Pullback hSetCategory {X = X} {Z = Y} {Y = X} f f
  KernelPair = hSetHasPullbacks f f

  Im : Ob
  Im = ∃[ b ] ∥ fiber f b ∥ , isOfHLevelΣ 2 (Y .snd) λ _ → isProp→isSet squash

  im : X ⟶ Im
  im x = f x , ∣ x , refl ∣

  open Pullback KernelPair

  lem : ∀ {H : Ob} (h : X ⟶ H) → h ∘ p₁ ≡ h ∘ p₂ → Σ[ f ⦂ (Im ⟶ H) ] Π[ x ⦂ Im .fst ] (∀ y → im y ≡ x → h y ≡ f x)
  lem {H = H} h eq = uniqueChoice R prf
    where
    R : Im .fst → H .fst → hProp _
    R w x .fst = ∀ y → im y ≡ w → h y ≡ x
    R w x .snd =  isOfHLevelΠ 1 λ _ → isOfHLevelΠ 1 λ _ → H .snd _ _

    prf : Π[ x ⦂ Im .fst ] ∃!′ (H .fst) (λ u → ∀ y → im y ≡ x → h y ≡ u)
    prf (xy , p) .fst = (λ { (z , r) → h z , λ y imy≡xyp → cong (_$ ((y , z) , cong fst imy≡xyp ; sym r)) eq }) ∥$∥ p
    prf (xy , p) .snd x₁ x₂ Px₁ Px₂ = rec (H .snd x₁ x₂) (λ { (z , zs) → sym (Px₁ z (ΣProp≡ (λ _ → squash) zs)) ; Px₂ z (ΣProp≡ (λ _ → squash) zs) } ) p

  lem₂ : ∀ (H : Ob) (h : X ⟶ H) (i : Im ⟶ H) (x : Im .fst) (hi : h ≡ i ∘ im) (eq : h ∘ p₁ ≡ h ∘ p₂) → i x ≡ lem {H = H} h eq .fst x
  lem₂ H h i x hi eq = rec (H .snd _ _) (λ { (y , ys) → (cong i (ΣProp≡ (λ _ → squash) (sym ys)) ; sym (cong (_$ y) hi)) ; lem {H = H} h eq .snd x y (ΣProp≡ (λ _ → squash) ys) }) (x .snd)

  hSetCoeq : Coequalizer hSetCategory {X = P} {Y = X} p₁ p₂
  hSetCoeq .Coequalizer.obj = Im
  hSetCoeq .Coequalizer.arr = im
  hSetCoeq .Coequalizer.equality = funExt λ x → ΣProp≡ (λ _ → squash) λ i → commute i x
  hSetCoeq .Coequalizer.coequalize {H = H} {h = h} eq = lem {H = H} h eq .fst
  hSetCoeq .Coequalizer.universal {H = H} {h = h} {eq = eq} = funExt λ x → lem {H = H} h eq .snd (im x) x refl
  hSetCoeq .Coequalizer.unique {H = H} {h = h} {i = i} {eq = eq} prf = funExt λ x → lem₂ H h i x prf eq
open CoeqProofs using (hSetCoeq) public

module PullbackSurjProofs {X Y : Ob} (f : X ⟶ Y) (fSurj : Surjective f) where
  KernelPair : Pullback hSetCategory {X = X} {Z = Y} {Y = X} f f
  KernelPair = hSetHasPullbacks f f

  open Pullback KernelPair

  p₁surj : Surjective p₁
  p₁surj y = ∣ ((y , y) , refl) , refl ∣

  p₂surj : Surjective p₂
  p₂surj y = ∣ ((y , y) , refl) , refl ∣

open import Relation.Binary
open import Cubical.HITs.SetQuotients

module _ {A : Type a} {R : A → A → Type b} {C : Type c}
         (isSetC : isSet C)
         (f : A → C)
         (coh : ∀ x y → R x y → f x ≡ f y)
         where

  recQuot : A / R → C
  recQuot [ a ] = f a
  recQuot (eq/ a b r i) = coh a b r i
  recQuot (squash/ xs ys x y i j) = isSetC (recQuot xs) (recQuot ys) (cong recQuot x) (cong recQuot y) i j

open import Path.Reasoning

module ExtactProofs {X : Ob} {R : X .fst → X .fst → hProp ℓ}
  (symR : Symmetric (λ x y → R x y .fst))
  (transR : Transitive (λ x y → R x y .fst))
  (reflR : Reflexive (λ x y → R x y .fst))
  where
  ℛ : X .fst → X .fst → Type ℓ
  ℛ x y = R x y .fst

  Src : Ob
  Src .fst = ∃[ x,y ] (uncurry ℛ x,y)
  Src .snd = isOfHLevelΣ 2 (X .snd ⟨×⟩ X .snd) λ _ → isProp→isSet (R _ _ .snd)

  pr₁ pr₂ : Src ⟶ X
  pr₁ = fst ∘ fst
  pr₂ = snd ∘ fst

  ROb : Ob
  ROb = X .fst / ℛ , squash/

  CR : Coequalizer hSetCategory {X = Src} {Y = X} pr₁ pr₂
  CR .Coequalizer.obj = ROb
  CR .Coequalizer.arr = [_]
  CR .Coequalizer.equality = funExt λ { ((x , y) , x~y) → eq/ x y x~y}
  CR .Coequalizer.coequalize {H = H} {h = h} e = recQuot (H .snd) h λ x y x~y → cong (_$ ((x , y) , x~y)) e
  CR .Coequalizer.universal {H = H} {h = h} {eq = e} = refl
  CR .Coequalizer.unique {H = H} {h = h} {i = i} {eq = e} p = funExt (elimProp (λ _ → H .snd _ _) λ x j → p (~ j) x)
