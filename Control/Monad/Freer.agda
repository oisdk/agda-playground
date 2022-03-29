{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Freer where

open import Prelude
open import Data.List hiding (map)
open import Data.List.Properties
open import Data.List.Membership
open import Algebra
open import Data.Fin hiding (fs)
open import Container


Distributes : (Type a → Type a) → (Type a → Type a) → Type _
Distributes F G = ∀ {A} → F (G A) → G (F A)

Freer : ∀ {ℓ₂ ℓ₃} → List (Container ℓ₂ ℓ₃) → Type (ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) → Type (ℓsuc (ℓ₂ ℓ⊔ ℓ₃))
Freer {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} fs A = foldr ⟦_⟧ A fs

module _ {ℓ₂ ℓ₃} where
  private
    variable f g : Container ℓ₂ ℓ₃
    variable fs gs : List (Container ℓ₂ ℓ₃)

  bind : Freer fs A → (A → Freer gs B) → Freer (fs ++ gs) B
  bind {fs = []} xs k = k xs
  bind {fs = f ∷ fs} xs k = cmap (flip (bind {fs = fs}) k) xs

  join : Freer fs (Freer gs A) → Freer (fs ++ gs) A
  join {fs = []} = id
  join {fs = f ∷ fs} = cmap (join {fs = fs})

  extend : Freer (fs ++ gs) A → (Freer gs A → B) → Freer fs B
  extend {fs = []}     x  k = (k x)
  extend {fs = f ∷ fs} xs k = cmap (flip (extend {fs = fs}) k) xs

  module _ {𝐹 : Type (ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) → Type (ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) }(mon : Monad 𝐹) where
    open import Data.Fin.Properties using (_<_)
    open Monad mon

    mmap : (A → B) → 𝐹 A → 𝐹 B
    mmap f xs = xs >>= return ∘ f

    handle : {A : Type (ℓsuc (ℓ₂ ℓ⊔ ℓ₃))} → (i : Fin (length fs)) →
             (⟦ fs ! i ⟧ ⇒ 𝐹) →
             (∀ j → j < i → Distributes ⟦ fs ! j ⟧ 𝐹) →
             Freer fs A →
             𝐹 (Freer (delete fs i) A)
    handle {fs = f ∷ fs} nothing  h d xs = h xs
    handle {fs = f ∷ fs} (just i) h d xs = d nothing tt (cmap (handle {fs = fs} i h (d ∘ just)) xs)

    handle″ : {A : Type (ℓsuc (ℓ₂ ℓ⊔ ℓ₃))} →
              (∀ j → Distributes 𝐹 ⟦ fs ! j ⟧) →
              𝐹 (Freer fs A) →
              Freer fs (𝐹 A)
    handle″ {fs = []}     d xs = xs
    handle″ {fs = f ∷ fs} d xs = cmap (handle″ {fs = fs} (d ∘ just)) (d f0 xs)

    handle′ : {A : Type (ℓsuc (ℓ₂ ℓ⊔ ℓ₃))} → (i : Fin (length fs)) →
              (⟦ fs ! i ⟧ ⇒ 𝐹) →
              (∀ j → i < j → Distributes 𝐹 ⟦ fs ! j ⟧) →
              Freer fs A →
              Freer (delete fs i) (𝐹 A)
    handle′ {fs = f ∷ fs} (just i) h d xs = cmap (handle′ {fs = fs} i h (d ∘ just)) xs
    handle′ {fs = f ∷ fs} nothing  h d xs = handle″ {fs = fs} (λ j → d (just j) tt) (h xs)

  -- module _ {ℓ₁} where
  --   gradedMonad : GradedMonad (listMonoid (Container ℓ₂ ℓ₃)) ℓ₁ _
  --   gradedMonad .GradedMonad.𝐹 = flip Freer
  --   gradedMonad .GradedMonad.return = lift
  --   gradedMonad .GradedMonad._>>=_ = bind
  --   gradedMonad .GradedMonad.>>=-idˡ f x = refl
  --   gradedMonad .GradedMonad.>>=-idʳ x = {!!}
  --   gradedMonad .GradedMonad.>>=-assoc = {!!}

-- --     gradedComonad : GradedComonad (listMonoid (Type ℓ₂ → Type ℓ₃)) ℓ₁ _
-- --     gradedComonad .GradedComonad.𝐹 = flip Freer
-- --     gradedComonad .GradedComonad.extract (pure x) = x
-- --     gradedComonad .GradedComonad._=>>_ = extend
-- --     gradedComonad .GradedComonad.=>>-idʳ f = refl
-- --     gradedComonad .GradedComonad.=>>-idˡ f = {!!}
-- --     gradedComonad .GradedComonad.=>>-assoc = {!!}
