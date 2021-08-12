{-# OPTIONS --without-K --safe #-}

module Function where

open import Level

infixr 9 _∘_ _∘′_
_∘_ : ∀ {A : Type a} {B : A → Type b} {C : {x : A} → B x → Type c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

_∘′_ : (B → C) → (A → B) → A → C
f ∘′ g = λ x → f (g x)
{-# INLINE _∘′_ #-}

flip : ∀ {A : Type a} {B : Type b} {C : A → B → Type c} →
        ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# INLINE flip #-}

id : ∀ {A : Type a} → A → A
id x = x
{-# INLINE id #-}

const : A → B → A
const x _ = x
{-# INLINE const #-}

infixr -1 _$_
_$_ : ∀ {A : Type a} {B : A → Type b}
      → (∀ (x : A) → B x)
      → (x : A)
      → B x
f $ x = f x
{-# INLINE _$_ #-}

infixl 0 _|>_
_|>_ : ∀ {A : Type a} {B : A → Type b}
      → (x : A)
      → (∀ (x : A) → B x)
      → B x
_|>_ = flip _$_
{-# INLINE _|>_ #-}

infixl 1 _⟨_⟩_
_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y
{-# INLINE _⟨_⟩_ #-}

infixl 0 _∋_
_∋_ : (A : Type a) → A → A
A ∋ x = x
{-# INLINE _∋_ #-}

infix 0 case_of_
case_of_ : A → (A → B) → B
case x of f = f x
{-# INLINE case_of_ #-}
