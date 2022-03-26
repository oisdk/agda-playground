module TraversalsMake where

open import Prelude
open import Data.Vec.Iterated


record Applicative (F : Type a → Type b) : Type (ℓsuc a ℓ⊔ b) where
  field
    pure  : A → F A
    _<*>_ : F (A → B) → F A → F B

  map : (A → B) → F A → F B
  map f x = ⦇ f x ⦈

open Applicative ⦃ ... ⦄

private variable F G : Type a → Type b

private variable n m : ℕ

travVec : ⦃ _ : Applicative F ⦄ → (A → F B) → Vec A n → F (Vec B n)
travVec {n = zero}  f _        = ⦇ [] ⦈
travVec {n = suc n} f (x ∷ xs) = ⦇ f x ∷ travVec f xs ⦈

record Traversed (T : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  field
    length   : ℕ
    contents : Vec A length
    rebuild  : ∀ {B} → Vec B length → T B

  traversed : ⦃ _ : Applicative F ⦄ → (A → F B) → F (T B)
  traversed f = map rebuild (travVec f contents)

open Traversed public

Traversal : (Type a → Type a) → Type _
Traversal T = T ⇒ Traversed T

traversing : ⦃ _ : Applicative F ⦄ → Traversal G → (A → F B) → G A → F (G B)
traversing t f xs = traversed (t xs) f
