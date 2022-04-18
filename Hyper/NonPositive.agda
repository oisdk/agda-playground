{-# OPTIONS --no-termination-check #-}

module Hyper.NonPositive where

open import Prelude

infixr 2 _↬_
{-# NO_POSITIVITY_CHECK #-}

record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor Φ; inductive
  infixl 4 _·_
  field _·_ : (B ↬ A) → B
open _↬_ public

_⊙_ : B ↬ C → A ↬ B → A ↬ C
(f ⊙ g) · k = f · (g ⊙ k)

𝕀 : A ↬ A
𝕀 · k = k · 𝕀

𝕂 : A ↬ B ↬ A
𝕂 · x · y = x · 𝕂

infixr 4 _◃_
_◃_ : (A → B) → A ↬ B → A ↬ B
(f ◃ h) · k = f (k · h)

infixl 4 _▹_
_▹_ : A ↬ B → (B → A) → A ↬ B
h ▹ f · k = h · (f ◃ k)

_◂_▸_ : ∀ {a′ b′} {A′ : Type a′} {B′ : Type b′} → (B → B′) → A ↬ B → (A′ → A) → A′ ↬ B′
(f ◂ h ▸ g) · k = f (h · (g ◂ k ▸ f))

mutual
  infixr 4 _◂_
  _◂_ : (B → C) → A ↬ B → A ↬ C
  (f ◂ h) · k = f (h · (k ▸ f))

  infixl 4 _▸_
  _▸_ : (B ↬ C) → (A → B) → A ↬ C
  h ▸ f · k = h · (f ◂ k)

△ : (A → B) → A ↬ B
△ f = f ◃ △ f

k : A → B ↬ A
k x · _ = x

▽ : A ↬ B → A → B
▽ h x = h · k x

ana : (A → (A → B) → C) → A → B ↬ C
ana ψ x · y = ψ x (λ z → y · ana ψ z)

cata : (((A → B) → C) → A) → B ↬ C → A
cata ϕ h = ϕ λ g → h · Φ (g ∘ cata ϕ)

unroll : A ↬ B → (A ↬ B → A) → B
unroll x f = x · Φ f

roll : ((A ↬ B → A) → B) → A ↬ B
roll f · k = f (k ·_)

𝕊 : A ↬ (B → C) → A ↬ B → A ↬ C
𝕊 = curry (ana λ { (i , j) fga → (i · Φ (fga ∘ (_, j))) (j · Φ (fga ∘ (i ,_))) })

𝕄 : A ↬ A ↬ B → A ↬ B
𝕄 h · k = h · Φ (λ x → k · 𝕄 x) · k

Producer : Type a → Type b → Type (a ℓ⊔ b)
Producer A B = (A → B) ↬ B

Consumer : Type a → Type b → Type (a ℓ⊔ b)
Consumer A B = B ↬ (A → B)

yield : A → Producer A B → Producer A B
yield x prod · cons = (cons · prod) x

await : (A → B → B) → Consumer A B → Consumer A B
(await f cons · prod) x = f x (prod · cons)

open import Data.List

zipˡ : List A → Producer A (List (A × B))
zipˡ = foldr yield (k [])

zipʳ : List B → Consumer A (List (A × B))
zipʳ = foldr (λ y → await (λ x xs → (x , y) ∷ xs)) (k λ _ → [])

zipʰ : List A → List B → List (A × B)
zipʰ xs ys = zipˡ xs · zipʳ ys

open import Relation.Binary

module Sorting {ℓ} {E : Type ℓ} (tot : TotalOrder E ℓzero ℓzero) where
  open TotalOrder tot

  nilˡ : Producer (Maybe E) (List E)
  nilˡ · yk = (yk · nilˡ) nothing

  mergeˡ : List E → Producer (Maybe E) (List E)
  mergeˡ = foldr (yield ∘ just) nilˡ

  nilʳ : Consumer (Maybe E) (List E)
  (nilʳ · xs) nothing  = []
  (nilʳ · xs) (just x) = x ∷ (xs · nilʳ)

  merge¹ : E → Consumer (Maybe E) (List E) → Consumer (Maybe E) (List E)
  (merge¹ y yk · xk) nothing  = y ∷ (xk · yk)
  (merge¹ y yk · xk) (just x) with x ≤? y
  ... | yes x≤y = x ∷ (xk · merge¹ y yk)
  ... | no  x≰y = y ∷ (yk · xk) (just x)

  mergeʳ : List E → Consumer (Maybe E) (List E)
  mergeʳ = foldr merge¹ nilʳ
