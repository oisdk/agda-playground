module Control.Monad.Free.Eff where

open import Prelude
open import Data.Set
open import Data.Set.Member
open import Data.Set.Union


module _ (Univ : Type) (⟦_⟧ : Univ → Type → Type) (_≟_ : Discrete Univ) where
  open WithDecEq _≟_

  private variable 
    F G : Univ
    Fs Gs : 𝒦 Univ

  data Eff (E : 𝒦 Univ) (A : Type) : Type₁ where
    pure : A → Eff E A
    Impure : (f∈ : F ∈ E) → (x : ⟦ F ⟧ B) → (k : B → Eff E A) → Eff E A

  -- bind : (A → Eff Fs B) → Eff Fs A → Eff Fs B
  -- bind k (pure x) = k x
  -- bind k (Impure f∈e x ks) = Impure f∈e x (bind k ∘ ks)

  -- weaken : Eff Fs A → Eff (Fs ∪ Gs) A
  -- weaken (pure x) = pure x
  -- weaken {Fs = Fs} (Impure f∈ x k) = Impure (◇-∪ _ Fs _ f∈) x (weaken ∘ k)

  -- weaken′ : Eff Fs A → Eff (Gs ∪ Fs) A
  -- weaken′ {Fs = Fs} {Gs = Gs} = subst (flip Eff _) (∪-com Fs Gs) ∘′ weaken

  -- bind′ : (A → Eff Gs B) → Eff Fs A → Eff (Fs ∪ Gs) B
  -- bind′ {Fs = Fs} k (pure x) = weaken′ {Gs = Fs} (k x)
  -- bind′ {Fs = Fs} k (Impure f∈e x ks) = Impure (◇-∪ _ Fs _ f∈e) x (bind′ k ∘ ks)

  -- extend′ : (Eff Gs A → B) → Eff (Fs ∪ Gs) A → Eff Fs B
  -- extend′ k (pure x) = pure (k (pure x))
  -- extend′ {Gs = Gs} {Fs = Fs} k (Impure {F = F} f∈ x ks) with F ∈? Gs 
  -- extend′ {Gs = Gs} {Fs = Fs} k (Impure {F = F} f∈ x ks) | yes F∈Gs = {!!}
  -- extend′ {Gs = Gs} {Fs = Fs} k (Impure {F = F} f∈ x ks) | no  F∉Gs = Impure {F = F} (◇⁻-∪ˡ F Fs Gs F∉Gs f∈) x (extend′ k ∘ ks)
