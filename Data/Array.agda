{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Array where

open import Data.Binary
open import Data.Binary.Increment
open import Prelude

private
  variable
    ns : 𝔹

record 2× {a} (A : Type a) : Type a where
  eta-equality
  constructor _⊛_
  field
    pr₁ pr₂ : A
open 2× public

infixr 5 _∷₁_ _∷₂_ _∷_

mutual
  record Array0ᵇ {a} : Type a where
    eta-equality
    constructor []

  record Array1ᵇ {a} (A : Type a) (ns : 𝔹) : Type a where
    eta-equality
    inductive
    constructor _∷₁_
    field
      head1ᵇ : A
      tail1ᵇ : Array (2× A) ns

  record Array2ᵇ {a} (A : Type a) (ns : 𝔹) : Type a where
    eta-equality
    inductive
    constructor _∷₂_
    field
      head2ᵇ : 2× A
      tail2ᵇ : Array (2× A) ns

  Array : Type a → 𝔹 → Type a
  Array A 0ᵇ = Array0ᵇ
  Array A (1ᵇ ns) = Array1ᵇ A ns
  Array A (2ᵇ ns) = Array2ᵇ A ns

_∷_ : A → Array A ns → Array A (inc ns)
_∷_ {ns = 0ᵇ} x xs = x ∷₁ xs
_∷_ {ns = 1ᵇ ns} x₁ (x₂ ∷₁ xs) = (x₁ ⊛ x₂) ∷₂ xs
_∷_ {ns = 2ᵇ ns} x₁ (x₂ ∷₂ xs) = x₁ ∷₁ x₂ ∷ xs

open import Lens

⦅head1ᵇ⦆ : Lens (Array A (1ᵇ ns)) A
⦅head1ᵇ⦆ .fst (x ∷₁ xs) = lens-part x (_∷₁ xs)
⦅head1ᵇ⦆ .snd .get-set xs v i = v
⦅head1ᵇ⦆ .snd .set-get xs i = xs
⦅head1ᵇ⦆ .snd .set-set (x ∷₁ xs) v₁ v₂ i = v₂ ∷₁ xs

⦅head2ᵇ⦆ : Lens (Array A (2ᵇ ns)) (2× A)
⦅head2ᵇ⦆ .fst (x ∷₂ xs) = lens-part x (_∷₂ xs)
⦅head2ᵇ⦆ .snd .get-set (x ∷₂ xs) v i = v
⦅head2ᵇ⦆ .snd .set-get (x ∷₂ xs) i = x ∷₂ xs
⦅head2ᵇ⦆ .snd .set-set (x ∷₂ xs) v₁ v₂ i = v₂ ∷₂ xs

⦅tail1ᵇ⦆ : Lens (Array A (1ᵇ ns)) (Array (2× A) ns)
⦅tail1ᵇ⦆ .fst (x ∷₁ xs) = lens-part xs (x ∷₁_)
⦅tail1ᵇ⦆ .snd .get-set (x ∷₁ xs) v i = v
⦅tail1ᵇ⦆ .snd .set-get (x ∷₁ xs) i = x ∷₁ xs
⦅tail1ᵇ⦆ .snd .set-set (x ∷₁ xs) v₁ v₂ i = x ∷₁ v₂

⦅tail2ᵇ⦆ : Lens (Array A (2ᵇ ns)) (Array (2× A) ns)
⦅tail2ᵇ⦆ .fst (x ∷₂ xs) = lens-part xs (x ∷₂_)
⦅tail2ᵇ⦆ .snd .get-set (x ∷₂ xs) v i = v
⦅tail2ᵇ⦆ .snd .set-get (x ∷₂ xs) i = x ∷₂ xs
⦅tail2ᵇ⦆ .snd .set-set (x ∷₂ xs) v₁ v₂ i = x ∷₂ v₂

⦅pr₁⦆ : Lens (2× A) A
⦅pr₁⦆ .fst (x ⊛ y) = lens-part x (_⊛ y)
⦅pr₁⦆ .snd .get-set s v i = v
⦅pr₁⦆ .snd .set-get s i = s
⦅pr₁⦆ .snd .set-set s v₁ v₂ i = v₂ ⊛ s .pr₂

⦅pr₂⦆ : Lens (2× A) A
⦅pr₂⦆ .fst (x ⊛ y) = lens-part y (x ⊛_)
⦅pr₂⦆ .snd .get-set s v i = v
⦅pr₂⦆ .snd .set-get s i = s
⦅pr₂⦆ .snd .set-set s v₁ v₂ i = s .pr₁ ⊛ v₂

open import Data.Binary.Order

mutual
  index : ∀ is {js} → is < js → Lens (Array A js) A
  index 0ᵇ      {1ᵇ js} p = ⦅head1ᵇ⦆
  index 0ᵇ      {2ᵇ js} p = ⦅head2ᵇ⦆ ⋯ ⦅pr₁⦆
  index (1ᵇ is) {js}    p = ind₂1ᵇ is p
  index (2ᵇ is) {1ᵇ js} p = ⦅tail1ᵇ⦆ ⋯ index is p ⋯ ⦅pr₂⦆
  index (2ᵇ is) {2ᵇ js} p = ⦅tail2ᵇ⦆ ⋯ index is p ⋯ ⦅pr₁⦆

  ind₂1ᵇ : ∀ is {js} → 1ᵇ is < js → Lens (Array A js) A
  ind₂1ᵇ is      {1ᵇ js} p = ⦅tail1ᵇ⦆ ⋯ index is p ⋯ ⦅pr₁⦆
  ind₂1ᵇ 0ᵇ      {2ᵇ js} p = ⦅head2ᵇ⦆ ⋯ ⦅pr₂⦆
  ind₂1ᵇ (1ᵇ is) {2ᵇ js} p = ⦅tail2ᵇ⦆ ⋯ ind₃ is p ⋯ ⦅pr₂⦆
  ind₂1ᵇ (2ᵇ is) {2ᵇ js} p = ⦅tail2ᵇ⦆ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₂⦆

  ind₂2ᵇ : ∀ is {js} → 2ᵇ is ≤ js → Lens (Array A js) A
  ind₂2ᵇ is      {1ᵇ js} p = ⦅tail1ᵇ⦆ ⋯ index is p ⋯ ⦅pr₁⦆
  ind₂2ᵇ 0ᵇ      {2ᵇ js} p = ⦅head2ᵇ⦆ ⋯ ⦅pr₂⦆
  ind₂2ᵇ (1ᵇ is) {2ᵇ js} p = ⦅tail2ᵇ⦆ ⋯ ind₃ is p ⋯ ⦅pr₂⦆
  ind₂2ᵇ (2ᵇ is) {2ᵇ js} p = ⦅tail2ᵇ⦆ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₂⦆

  ind₃ : ∀ is {js} → 1ᵇ is ≤ js → Lens (Array A js) A
  ind₃ 0ᵇ      {1ᵇ js} p = ⦅head1ᵇ⦆
  ind₃ 0ᵇ      {2ᵇ js} p = ⦅head2ᵇ⦆ ⋯ ⦅pr₁⦆
  ind₃ (1ᵇ is) {1ᵇ js} p = ⦅tail1ᵇ⦆ ⋯ ind₃ is p ⋯ ⦅pr₂⦆
  ind₃ (1ᵇ is) {2ᵇ js} p = ⦅tail2ᵇ⦆ ⋯ ind₃ is p ⋯ ⦅pr₁⦆
  ind₃ (2ᵇ is) {1ᵇ js} p = ⦅tail1ᵇ⦆ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₂⦆
  ind₃ (2ᵇ is) {2ᵇ js} p = ⦅tail2ᵇ⦆ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₁⦆

at : ∀ is {js} → {p : is < js} → Lens (Array A js) A
at is {p = p} = index is p

import Data.Nat as ℕ

foldrP : ∀ {p} (P : ℕ → Type p) → (∀ {n} → A → P n → P (suc n)) → P zero → Array A ns → P ⟦ ns ⇓⟧
foldrP {ns = 0ᵇ} P f b [] = b
foldrP {ns = 1ᵇ ns} P f b (x ∷₁ xs) = f x (foldrP (λ n → P (n ℕ.* 2)) (λ { (x₁ ⊛ x₂) b → f x₁ (f x₂ b) }) b xs)
foldrP {ns = 2ᵇ ns} P f b ((x₁ ⊛ x₂) ∷₂ xs) = f x₁ (f x₂ (foldrP (λ n → P (n ℕ.* 2)) (λ { (x₁ ⊛ x₂) b → f x₁ (f x₂ b)}) b xs))

foldr : (A → B → B) → B → Array A ns → B
foldr f b = foldrP (λ _ → _) f b

map : (A → B) → Array A ns → Array B ns
map {ns = 0ᵇ}    f xs = []
map {ns = 1ᵇ ns} f (x ∷₁ xs) = f x ∷₁ map (λ { (x₁ ⊛ x₂) → f x₁ ⊛ f x₂ }) xs
map {ns = 2ᵇ ns} f ((x₁ ⊛ x₂) ∷₂ xs) = (f x₁ ⊛ f x₂) ∷₂ map (λ { (x₁ ⊛ x₂) → f x₁ ⊛ f x₂ }) xs

import Data.List as List
open import Data.List using (List)

toList : Array A ns → List.List A
toList = foldr List._∷_ List.[]

fromList : (xs : List A) → Array A ⟦ List.length xs ⇑⟧
fromList List.[] = []
fromList (x List.∷ xs) = x ∷ fromList xs

-- Lens laws are satisfied definitionally:

-- get-set
_ : (xs : Array ℕ ⟦ 10 ⇑⟧) (n : ℕ) →  (xs [ at ⟦ 5 ⇑⟧ ]≔ n [ at ⟦ 5 ⇑⟧ ]) ≡ n
_ = λ xs n → refl

-- set-get
_ : (xs : Array ℕ ⟦ 10 ⇑⟧) → (xs [ at ⟦ 5 ⇑⟧ ]≔ (xs [ at ⟦ 5 ⇑⟧ ])) ≡ xs
_ = λ xs → refl

-- set-set
_ : (xs : Array ℕ ⟦ 10 ⇑⟧) (n m : ℕ) → (xs [ at ⟦ 5 ⇑⟧ ]≔ n [ at ⟦ 5 ⇑⟧ ]≔ m) ≡ (xs [ at ⟦ 5 ⇑⟧ ]≔ m)
_ = λ xs n m → refl
