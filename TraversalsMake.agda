{-# OPTIONS --allow-unsolved-metas #-}

module TraversalsMake where

open import Prelude
open import Data.Vec.Iterated

record Applicative (F : Type a → Type b) : Type (ℓsuc a ℓ⊔ b) where
  infixl 5 _<*>_
  field
    pure  : A → F A
    _<*>_ : F (A → B) → F A → F B

    identity : (x : F A) → ⦇ id x ⦈ ≡ x
    composition : ∀ (x : F (B → C)) (y : F (A → B)) (z : F A) → ⦇ _∘′_ x y z ⦈ ≡ x <*> (y <*> z)
    homomorphism : (f : A → B) (x : A) → ⦇ f ⦇ x ⦈ ⦈ ≡ ⦇ (f x) ⦈
    interchange : (x : F (A → B)) (y : A) → x <*> pure y ≡ ⦇ (_$ y) x ⦈

  _*>_ : F A → F B → F B
  xs *> ys = ⦇ (λ _ y → y) xs ys ⦈

  _<*_ : F A → F B → F A
  xs <* ys = ⦇ (λ x _ → x) xs ys ⦈

  map : (A → B) → F A → F B
  map f x = ⦇ f x ⦈

open Applicative ⦃ ... ⦄ public

private variable F G : Type a → Type a

private variable n m : ℕ

ap : ⦃ _ : Applicative F ⦄ → (A → F B) → Vec A n → F (Vec B n)
ap {n = zero}  f _        = ⦇ [] ⦈
ap {n = suc n} f (x ∷ xs) = ⦇ f x ∷ ap f xs ⦈

record Traversed (T : Type a → Type a) (A : Type a) : Type (ℓsuc a) where
  field
    length   : ℕ
    contents : Vec A length
    rebuild  : ∀ {B} → Vec B length → T B

record Traversable (T : Type a → Type a) : Type (ℓsuc a) where
  field
    traversed : ∀ {A} → T A → Traversed T A

  traverse : ⦃ _ : Applicative F ⦄ → (A → F B) → T A → F (T B)
  traverse f xs = ⦇ rebuild (ap f contents) ⦈
    where open Traversed (traversed xs)

open Traversable ⦃ ... ⦄

Commutes : ∀ {F : Type a → Type b} ⦃ _ : Applicative F ⦄ → F A → F B → Type _
Commutes xs ys = ⦇ xs , ys ⦈ ≡ ⦇ (flip _,_) ys xs ⦈

open import Path.Reasoning

_⊛>_ : ⦃ _ : Applicative F ⦄ → (A → F B) → (A → F C) → A → F C
(f ⊛> g) x = f x *> g x

module _ {A B} (f g : A → F B) ⦃ _ : Applicative F ⦄ (comm : ∀ x → Commutes (f x) (g x)) {G} ⦃ _ : Traversable G ⦄ where
  trav-flip : (xs : G A) → (traverse f ⊛> traverse g) xs ≡ traverse (f ⊛> g) xs
  trav-flip container = distrib ; cong (map rebuild) (go length contents)
    where
    open Traversed (traversed container)

    distrib : traverse f container *> traverse g container ≡ ⦇ rebuild (ap f contents *> ap g contents) ⦈
    distrib =
      traverse f container *> traverse g container ≡⟨⟩
      ⦇ rebuild (ap f contents) ⦈ *> ⦇ rebuild (ap g contents) ⦈ ≡⟨ {!!} ⟩
      ⦇ rebuild (ap f contents *> ap g contents) ⦈ ∎

    go : ∀ n → (xs : Vec A n) → ap f xs *> ap g xs ≡ ap (f ⊛> g) xs
    go zero    []       =
      ⦇ [] ⦈ *> ⦇ [] ⦈ ≡⟨ {!!} ⟩
      ⦇ [] ⦈ ∎

    go (suc n) (x ∷ xs) =
      ap f (x ∷ xs) *> ap g (x ∷ xs) ≡⟨⟩
      ⦇ f x ∷ ap f xs ⦈ *> ⦇ g x ∷ ap g xs ⦈ ≡⟨ {!!} ⟩
      ⦇ (f x *> g x) ∷ (ap f xs *> ap g xs) ⦈ ≡⟨ cong (λ r → ⦇ (f x *> g x) ∷ r ⦈ ) (go n xs) ⟩
      ⦇ (f x *> g x) ∷ ap (f ⊛> g) xs ⦈ ≡⟨⟩
      ap (f ⊛> g) (x ∷ xs) ∎

