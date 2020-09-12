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
discreteMaybe _≟_ (just x) (just y) = ⟦yes cong just ,no just-inj ⟧ (x ≟ y)
