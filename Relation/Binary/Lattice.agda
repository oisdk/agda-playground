{-# OPTIONS --cubical --safe #-}

open import Prelude hiding (sym; refl)
open import Relation.Binary

module Relation.Binary.Lattice {ℓ₁ ℓ₂ ℓ₃} {𝑆 : Type ℓ₁} (totalOrder : TotalOrder 𝑆 ℓ₂ ℓ₃) where

open TotalOrder totalOrder

import Path as ≡

min-max : 𝑆 → 𝑆 → 𝑆 × 𝑆
min-max x y = bool′ (y , x) (x , y) (x <ᵇ y)

_⊔_ : 𝑆 → 𝑆 → 𝑆
x ⊔ y = snd (min-max x y)

_⊓_ : 𝑆 → 𝑆 → 𝑆
x ⊓ y = fst (min-max x y)

min-max-assoc : ∀ x y z → map-Σ (_⊓ z) (_⊔ z) (min-max x y) ≡ map-Σ (x ⊓_) (x ⊔_) (min-max y z)
min-max-assoc x y z with x <? y | inspect (x <ᵇ_) y | y <? z | inspect (y <ᵇ_) z
min-max-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 with x <? z
min-max-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | yes x≤z = cong₂ _,_ (cong (fst ∘ bool _ _) (≡.sym xyp)) (cong (snd ∘ bool _ _) yzp)
min-max-assoc x y z | yes x≤y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 | no  x≥z = ⊥-elim (x≥z (<-trans x≤y y≤z))
min-max-assoc x y z | no  x≥y | 〖 xyp 〗 | yes y≤z | 〖 yzp 〗 = cong (_, (x ⊔ z)) (cong (fst ∘ bool _ _) yzp ; cong (fst ∘ bool _ _) (≡.sym xyp))
min-max-assoc x y z | yes x≤y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 = cong ((x ⊓ z) ,_) (cong (snd ∘ bool _ _) yzp ; cong (snd ∘ bool _ _) (≡.sym xyp))
min-max-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 with x <? z
min-max-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | yes x≤z = let z≡x = antisym (≤-trans (≮⇒≥ y≥z) (≮⇒≥ x≥y)) (<⇒≤ x≤z) in cong₂ _,_ (cong (fst ∘ bool _ _) yzp ; z≡x) (z≡x ; cong (snd ∘ bool _ _) (≡.sym xyp))
min-max-assoc x y z | no  x≥y | 〖 xyp 〗 | no  y≥z | 〖 yzp 〗 | no  x≥z = cong₂ _,_ (cong (fst ∘ bool _ _) yzp) (cong (snd ∘ bool _ _) (≡.sym xyp))

⊓-assoc : ∀ x y z → (x ⊓ y) ⊓ z ≡ x ⊓ (y ⊓ z)
⊓-assoc x y z = cong fst (min-max-assoc x y z)

⊔-assoc : ∀ x y z → (x ⊔ y) ⊔ z ≡ x ⊔ (y ⊔ z)
⊔-assoc x y z = cong snd (min-max-assoc x y z)

min-max-comm : ∀ x y → min-max x y ≡ min-max y x
min-max-comm x y with x <? y | y <? x
min-max-comm x y | yes x<y | yes y<x = ⊥-elim (asym x<y y<x)
min-max-comm x y | no  x≮y | yes y<x = ≡.refl
min-max-comm x y | yes x<y | no  y≮x = ≡.refl
min-max-comm x y | no  x≮y | no  y≮x = cong₂ _,_ (conn y≮x x≮y) (conn x≮y y≮x)

⊓-comm : ∀ x y → x ⊓ y ≡ y ⊓ x
⊓-comm x y = cong fst (min-max-comm x y)

⊔-comm : ∀ x y → x ⊔ y ≡ y ⊔ x
⊔-comm x y = cong snd (min-max-comm x y)

min-max-idem : ∀ x → min-max x x ≡ (x , x)
min-max-idem x = bool {P = λ r → bool′ (x , x) (x , x) r ≡ (x , x)} ≡.refl ≡.refl (x <ᵇ x)

⊓-idem : ∀ x → x ⊓ x ≡ x
⊓-idem x = cong fst (min-max-idem x)

⊔-idem : ∀ x → x ⊔ x ≡ x
⊔-idem x = cong snd (min-max-idem x)

≤⊔ : ∀ x y → x ≤ x ⊔ y
≤⊔ x y with x <? y
≤⊔ x y | yes x<y = <⇒≤ x<y
≤⊔ x y | no  x≮y = refl

⊓≤ : ∀ x y → x ⊓ y ≤ x
⊓≤ x y with x <? y
⊓≤ x y | yes x<y = refl
⊓≤ x y | no  x≮y = ≮⇒≥ x≮y
