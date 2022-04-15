{-# OPTIONS --no-termination-check #-}

module Hyper.NonStrictPositive where

open import Prelude

infixr 0 _↬_ _↬′_
_↬′_ : Type a → Type b → Type (a ℓ⊔ b)

{-# NO_POSITIVITY_CHECK #-}
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive
  infixl 4 _·_
  field _·_ : (k : B ↬′ A) → B

A ↬′ B = (k : B ↬ A) → B

open _↬_ public 


infixl 4 _·′_
_·′_ : (A → B) → (A → B)
_·′_ = id
{-# INLINE _·′_ #-}

infixr 9 _⊙_
_⊙_ : B ↬ C → A ↬ B → A ↬ C
f₁ ⊙ f₂ · f₃ = f₁ · λ f₄ → f₂ · λ f₅ → f₃ ·′ (f₄ ⊙ f₅)

cata : (((C → A) → B) → C) → A ↬ B → C
cata ϕ h = ϕ λ k → h · k ∘ cata ϕ

ana : (C → (C → A) → B) → C → A ↬ B
ana ψ r · k = ψ r (k ∘ ana ψ)

𝕀 : A ↬ A
𝕀 · x = x ·′ 𝕀

𝕀′ : A ↬′ A
𝕀′ x = x · 𝕀′

pure : A → B ↬ A
pure x · _ = x

𝕂 : A ↬ B ↬ A
𝕂 · x · y = x ·′ 𝕂

_<*>_ : A ↬ (B → C) → A ↬ B → A ↬ C
_<*>_ = curry (ana λ { (i , j) fga → (i · fga ∘ (_, j)) (j · fga ∘ (i ,_)) })

𝕄 : A ↬ A ↬ B → A ↬ B
𝕄 = cata λ where g · k → g ·′ k · k

_◃_ : (A → B) → A ↬ B → A ↬ B
(f ◃ h) · k = f (k ·′ h)

△ : (A → B) → A ↬ B
△ f = f ◃ △ f

▽ : A ↬ B → A → B
▽ h x = h · λ _ → x

infixr 2 _↝_
data Tree (A : Type a) : Type a where
  [_] : A → Tree A
  _↝_ : Tree A → Tree A → Tree A

⟦_⟧ₜ : Tree (Type a) → Type a
⟦ [ A ] ⟧ₜ = A
⟦ x ↝ y ⟧ₜ = ⟦ x ⟧ₜ → ⟦ y ⟧ₜ

⟦_⟧ₕ : Tree (Type a) → Type a
⟦ [ A ] ⟧ₕ = A
⟦ x ↝ y ⟧ₕ = ⟦ x ⟧ₕ ↬ ⟦ y ⟧ₕ

mutual
  ⟦_⟧↑ : (t : Tree (Type a)) → ⟦ t ⟧ₜ → ⟦ t ⟧ₕ
  ⟦ [ _ ] ⟧↑ x = x
  ⟦ x ↝ y ⟧↑ f = △ (⟦ y ⟧↑ ∘ f ∘ ⟦ x ⟧↓)  

  ⟦_⟧↓ : (t : Tree (Type a)) → ⟦ t ⟧ₕ → ⟦ t ⟧ₜ
  ⟦ [ _ ] ⟧↓ x = x
  ⟦ x ↝ y ⟧↓ f = ⟦ y ⟧↓ ∘ ▽ f ∘ ⟦ x ⟧↑

module _ {A B C : Type a} where
  𝕊 : (A ↬ B ↬ C) ↬ (A ↬ B) ↬ A ↬ C
  𝕊 = ⟦ ([ A ] ↝ [ B ] ↝ [ C ]) ↝ ([ A ] ↝ [ B ]) ↝ [ A ] ↝ [ C ] ⟧↑ λ x y z → (x z) (y z)  

run : A ↬ A → A
run h = h · 𝕀′

eval : ((A ↬ B) × A) ↬ B
eval · k = uncurry ▽ (k eval)
