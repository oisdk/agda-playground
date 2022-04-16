{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Properties where

open import Data.Maybe.Base
open import Prelude

fromMaybe : A → Maybe A → A
fromMaybe x = maybe x id

just-inj : ∀ {x y : A} → just x ≡ just y → x ≡ y
just-inj {x = x} = cong (fromMaybe x)

just≢nothing : {x : A} → just x ≢ nothing
just≢nothing p = subst (maybe ⊥ (const ⊤)) p tt

nothing≢just : {x : A} → nothing ≢ just x
nothing≢just p = subst (maybe ⊤ (const ⊥)) p tt

discreteMaybe : Discrete A → Discrete (Maybe A)
discreteMaybe _≟_ nothing nothing = yes refl
discreteMaybe _≟_ nothing (just x) = no nothing≢just
discreteMaybe _≟_ (just x) nothing = no just≢nothing
discreteMaybe _≟_ (just x) (just y) = iff-dec (cong just iff just-inj) (x ≟ y)

is-just : Maybe A → Bool
is-just = maybe false (const true)

IsJust : Maybe A → Type
IsJust = T ∘ is-just

fromJust : (x : Maybe A) → ⦃ IsJust x ⦄ → A
fromJust (just x) = x

open import Algebra 

maybeFunctor : Functor {ℓ₁ = a} Maybe
maybeFunctor .Functor.map = mapMaybe
maybeFunctor .Functor.map-id = funExt λ { nothing → refl ; (just x) → refl }
maybeFunctor .Functor.map-comp f g = funExt λ { nothing → refl ; (just x) → refl }

maybeMonad : Monad {ℓ₁ = a} Maybe
(maybeMonad Monad.>>= nothing) y = nothing
(maybeMonad Monad.>>= just x) y = y x
maybeMonad .Monad.return = just
maybeMonad .Monad.>>=-idˡ f x = refl
maybeMonad .Monad.>>=-idʳ nothing = refl
maybeMonad .Monad.>>=-idʳ (just x) = refl
maybeMonad .Monad.>>=-assoc nothing f g = refl
maybeMonad .Monad.>>=-assoc (just x) f g = refl
