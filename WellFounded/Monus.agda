module WellFounded.Monus where

open import Prelude
open import Algebra.Monus

module _ {ℓ} (mon : TMAPOM ℓ) where
  open TMAPOM mon

  Within : 𝑆 → Type a → Type _
  Within x A = Acc _<_ x → A

  extract : Within ε A → A
  extract xs = xs (acc λ { y y<ε → ⊥-elim (y<ε (positive y)) })

  cmb : ∀ {x y} → Acc _<_ x → Acc _<_ y → Acc _<_ (x ∙ y)
  cmb {x} {y} (acc ax) (acc ay) =
    acc λ z z<x∙y →
      case x ≤? z of
        λ { (yes (k , z≡x∙k)) → subst (Acc _<_) (sym z≡x∙k) (cmb (acc ax) (ay k (≲[ ≡[ sym z≡x∙k ] ≲; <[ z<x∙y ] ] ∘′ ≤-cong _)))
          ; (no z<x) → ax z z<x }

  duplicate : ∀ {x y} → Within (x ∙ y) A → Within x (Within y A)
  duplicate x wx wy = x (cmb wx wy)

  reduce : ∀ {x y} → Acc _<_ (x ∙ y) → Acc _<_ x
  reduce {x} {y} axy with x ∙ y ≤? x
  reduce {x} {y} (acc axy) | no ¬p = axy _ ¬p
  reduce {x} {y} axy | yes p = subst (Acc _<_) (antisym p x≤x∙y) axy

  join : ∀ {x y} → Within x (Within y A) → Within (x ∙ y) A
  join {x = x} {y} xs axy = xs (reduce axy) (reduce (subst (Acc _<_) (comm _ _) axy))

  return : A → Within ε A
  return x _ = x

open import Function.Surjective
open import Function.Injective

_≺_ : Type → Type → Type
A ≺ B = ¬ (B ↣ A)

proof : ⊤ ≺ Bool
proof (f , inj) = subst (bool ⊥ ⊤)  (inj true false refl) tt

-- cmb′ : Acc _≺_ A → Acc _≺_ B → Acc _≺_ (A ⊎ B)
-- cmb′ {A} {B} (acc a) (acc b) = acc {!!}
