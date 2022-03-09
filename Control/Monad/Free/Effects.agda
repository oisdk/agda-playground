{-# OPTIONS --no-positivity-check --cubical --without-K #-}

module Control.Monad.Free.Effects where

open import Prelude
open import Data.Set.Definition
open import Data.Set.Eliminators
open import Data.Set.Member

module _ (Univ : Type) ([_] : Univ → Type → Type) (_≟_ : Discrete Univ) where
  open WithDecEq _≟_

  private
    variable
      F G : Univ
      Fs Gs : 𝒦 Univ

  mutual
    Free : 𝒦 Univ → Type → Type
    Free = flip Free′ 

    data Free′ (A : Type) : 𝒦 Univ → Type where
      ret : A → Free ∅ A 
      op : [ F ] (Free Fs A) → Free (F ∷ Fs) A

  open import Algebra

  module _ (mon : Monad ℓzero ℓzero) where
    open Monad mon

    mmap : (A → B) → 𝐹 A → 𝐹 B
    mmap f xs = xs >>= return ∘′ f

    module _ (traverse : ∀ {F A B} → (A → 𝐹 B) → [ F ] A → 𝐹 ([ F ] B)) where
      module _ (E : Univ) where
        interp : ([ E ] ⇒ 𝐹) → Free Fs A → 𝐹 (Free (Fs \\ E) A)
        interp ψ (ret x) = return (ret x)
        interp ψ (op {F = F} x) with E ≟ F
        ... | no  _   = mmap op (traverse (interp ψ) x)
        ... | yes E≡F = traverse (interp ψ) x >>= subst (λ G → [ G ] _ → 𝐹 _) E≡F ψ 
