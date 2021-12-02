{-# OPTIONS --allow-unsolved-metas #-}

module Control.Monad.Freer where

open import Prelude
open import Data.List hiding (map)
open import Data.List.Properties
open import Data.List.Membership
open import Algebra
open import Data.Fin hiding (fs)

data Freer {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) : List (Type ℓ₂ → Type ℓ₃) → Type (ℓ₁ ℓ⊔ ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) where
  pure : A → Freer A []
  call : ∀ {f fs x} → f x → (x → Freer A fs) → Freer A (f ∷ fs)


module _ {ℓ₂ ℓ₃} where
  private
    variable f g : Type ℓ₂ → Type ℓ₃
    variable fs gs : List (Type ℓ₂ → Type ℓ₃)

  bind : Freer A fs → (A → Freer B gs) → Freer B (fs ++ gs)
  bind (pure x) k = k x
  bind (call x xs) k = call x λ y → bind (xs y) k

  extend : Freer A (fs ++ gs) → (Freer A gs → B) → Freer B fs
  extend {fs = []} x k = pure (k x)
  extend {fs = f ∷ fs} (call x xs) k = call x λ y → extend (xs y) k

  -- module _ (mon : Monad _ _) where
  --   open Monad mon

  --   handle : (i : Fin (length fs)) → (fs ! i ⇒ 𝐹) → Freer A fs → 𝐹 (Freer A (delete fs i))
  --   handle {fs = f ∷ fs} nothing  h (call x k) = h x >>= λ y → return (k y)
  --   handle {fs = f ∷ fs} (just i) h (call x k) = {!!} >>= λ y → return (call x y)

  module _ {ℓ₁} where
    gradedMonad : GradedMonad (listMonoid (Type ℓ₂ → Type ℓ₃)) ℓ₁ _
    gradedMonad .GradedMonad.𝐹 = flip Freer
    gradedMonad .GradedMonad.pure = pure
    gradedMonad .GradedMonad._>>=_ = bind
    gradedMonad .GradedMonad.>>=-idˡ f x = refl
    gradedMonad .GradedMonad.>>=-idʳ x = {!!}
    gradedMonad .GradedMonad.>>=-assoc = {!!}

    gradedComonad : GradedComonad (listMonoid (Type ℓ₂ → Type ℓ₃)) ℓ₁ _
    gradedComonad .GradedComonad.𝐹 = flip Freer
    gradedComonad .GradedComonad.extract (pure x) = x
    gradedComonad .GradedComonad._=>>_ = extend
    gradedComonad .GradedComonad.=>>-idʳ f = refl
    gradedComonad .GradedComonad.=>>-idˡ f = {!!}
    gradedComonad .GradedComonad.=>>-assoc = {!!}
