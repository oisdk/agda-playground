{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Freer where

open import Prelude
open import Data.List hiding (map)
open import Data.List.Properties
open import Data.List.Membership
open import Algebra
open import Data.Fin hiding (fs)
open import Container

data Freer {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) : List (Container ℓ₂ ℓ₃) → Type (ℓ₁ ℓ⊔ ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) where
  pure : A → Freer A []
  call : ∀ {f fs} → ⟦ f ⟧ (Freer A fs) → Freer A (f ∷ fs)


module _ {ℓ₂ ℓ₃} where
  private
    variable f g : Container ℓ₂ ℓ₃
    variable fs gs : List (Container ℓ₂ ℓ₃)

  bind : Freer A fs → (A → Freer B gs) → Freer B (fs ++ gs)
  bind (pure x) k = k x
  bind (call xs) k = call (cmap (flip bind k) xs)

  extend : Freer A (fs ++ gs) → (Freer A gs → B) → Freer B fs
  extend {fs = []}     x k = pure (k x)
  extend {fs = f ∷ fs} (call xs) k = call (cmap (flip extend k) xs)

  module _ (mon : Monad _ _) where
    open Monad mon

    handle : (i : Fin (length fs)) → (⟦ fs ! i ⟧ ⇒ 𝐹) → Freer A fs → 𝐹 (Freer A (delete fs i))
    handle {fs = f ∷ fs} nothing  h (call xs) = h xs
    handle {fs = f ∷ fs} (just i) h (call xs) = {!!}

--   module _ {ℓ₁} where
--     gradedMonad : GradedMonad (listMonoid (Type ℓ₂ → Type ℓ₃)) ℓ₁ _
--     gradedMonad .GradedMonad.𝐹 = flip Freer
--     gradedMonad .GradedMonad.pure = pure
--     gradedMonad .GradedMonad._>>=_ = bind
--     gradedMonad .GradedMonad.>>=-idˡ f x = refl
--     gradedMonad .GradedMonad.>>=-idʳ x = {!!}
--     gradedMonad .GradedMonad.>>=-assoc = {!!}

--     gradedComonad : GradedComonad (listMonoid (Type ℓ₂ → Type ℓ₃)) ℓ₁ _
--     gradedComonad .GradedComonad.𝐹 = flip Freer
--     gradedComonad .GradedComonad.extract (pure x) = x
--     gradedComonad .GradedComonad._=>>_ = extend
--     gradedComonad .GradedComonad.=>>-idʳ f = refl
--     gradedComonad .GradedComonad.=>>-idˡ f = {!!}
--     gradedComonad .GradedComonad.=>>-assoc = {!!}
