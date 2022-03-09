module Control.Monad.Free.ListedEffects where

open import Prelude
open import Container renaming (Container to Container′)
open import Data.List

Container : _
Container = Container′ ℓzero ℓzero

private
  variable
    F G : Container
    Fs Gs : List Container

Free : List Container → Type → Type
Free = flip (foldr ⟦_⟧)

extract : Free [] A → A
extract x = x

open import Data.List.Properties

module _ {Fs Gs : List Container} {A B : Type} where
  extend : (Free Gs A → B) → Free (Fs ++ Gs) A → Free Fs B
  extend k = list-elim (λ Fs → Free (Fs ++ Gs) A → Free Fs B) (λ _ _ → cmap) k Fs

  _>>=_ : Free Fs A → (A → Free Gs B) → Free (Fs ++ Gs) B
  _>>=_ xs k = list-elim (λ Fs → Free Fs A → Free (Fs ++ Gs) B) (λ _ _ → cmap) k Fs xs
