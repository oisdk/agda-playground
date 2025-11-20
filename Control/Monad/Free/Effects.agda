module Control.Monad.Free.Effects where

open import Prelude
open import Data.Set.Definition
open import Data.Set.Member
open import Data.Set.Union
open import Data.Set.Empty
open import Container renaming (⟦_⟧ to ⟦_⟧′)

module _ (Univ : Type) (univ : Univ → Container) (_≟_ : Discrete Univ) where
  open WithDecEq _≟_

  ⟦_⟧ : Univ → Type → Type
  ⟦_⟧ = ⟦_⟧′ ∘ univ

  private
    variable
      F G : Univ
      Fs Gs : 𝒦 Univ

  mutual
    Free : 𝒦 Univ → Type → Type
    Free = flip Free′ 

    data Free′ (A : Type) : 𝒦 Univ → Type where
      ret : A → Free ∅ A 
      op : ⟦ F ⟧ (Free Fs A) → Free (F ∷ Fs) A

  open import Algebra

  module MonadInst where
    {-# TERMINATING #-}
    _>>=_ : Free Fs A → (A → Free Gs B) → Free (Fs ∪ Gs) B
    ret x >>= k = k x
    op x  >>= k = op (cmap (_>>= k) x)

    extract′ : Empty Fs → Free Fs A → A
    extract′ p (ret x) = x

    extract : Free ∅ A → A
    extract = extract′ tt

  module _ {𝐹 : Type → Type} (mon : Monad 𝐹) where
    open Monad mon

    module _ (traverse : ∀ {F A B} → (A → 𝐹 B) → ⟦ F ⟧ A → 𝐹 (⟦ F ⟧ B)) where
      module _ (E : Univ) where
        {-# TERMINATING #-}
        interp : (⟦ E ⟧ ⇒ 𝐹) → Free Fs A → 𝐹 (Free (Fs \\ E) A)
        interp ψ (ret x) = return (ret x)
        interp ψ (op {F = F} x) with E ≟ F
        ... | no  _   = mmap op (traverse (interp ψ) x)
        ... | yes E≡F = traverse (interp ψ) x >>= subst (λ G → ⟦ G ⟧ _ → 𝐹 _) E≡F ψ 
