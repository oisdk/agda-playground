module Traversable where

open import Prelude
open import Algebra
open import Applicative

private variable F G : Type a → Type b

module _ where
  open Algebra.Applicative ⦃ ... ⦄

  record Traversable (T : Type a → Type a) : Type (ℓsuc a) where
    field
      traverse : {F : Type a → Type a} ⦃ applicative : Applicative F ⦄ → (A → F B) → T A → F (T B)
      identity : (xs : T A) → traverse ⦃ applicative = idApplicative ⦄ id xs ≡ xs
      compose : {F G : Type a → Type a} ⦃ _ : Applicative F ⦄ ⦃ _ : Applicative G ⦄ →
                (f : B → F C) (g : A → G B) →
                (xs : T A) →
                map (traverse f) (traverse g xs) ≡ traverse ⦃ applicative = composeApplicative it it ⦄ (map f ∘ g) xs
      

