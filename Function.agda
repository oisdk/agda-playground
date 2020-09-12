{-# OPTIONS --cubical --safe #-}

module Function where

open import Level
open import Path

infixr 9 _∘_ _∘′_
_∘_ : ∀ {A : Type a} {B : A → Type b} {C : {x : A} → B x → Type c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

_∘′_ : (B → C) → (A → B) → A → C
f ∘′ g = λ x → f (g x)

flip : ∀ {A : Type a} {B : Type b} {C : A → B → Type c} →
        ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

id : ∀ {A : Type a} → A → A
id x = x

const : A → B → A
const x _ = x

infixr -1 _$_
_$_ : ∀ {A : Type a} {B : A → Type b}
      → (∀ (x : A) → B x)
      → (x : A)
      → B x
f $ x = f x

infixl 1 _⟨_⟩_
_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

infixl 0 _∋_
_∋_ : (A : Type a) → A → A
A ∋ x = x

infix 0 case_of_
case_of_ : A → (A → B) → B
case x of f = f x

record Reveal_·_is_ {A : Type a} {B : A → Type b} (f : (x : A) → B x) (x : A) (y : B x) : Type b where
  constructor 〖_〗
  field eq : f x ≡ y

inspect : {A : Type a} {B : A → Type b} (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = 〖 refl 〗
