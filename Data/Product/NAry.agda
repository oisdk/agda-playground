{-# OPTIONS --safe --cubical #-}

module Data.Product.NAry where

open import Data.Sigma
open import Prelude hiding (⊤; tt)
open import Data.Unit.UniversePolymorphic
open import Path.Reasoning

private
  variable
    n : ℕ
    ℓ : Level

Levels : ℕ → Type₀
Levels zero = ⊤
Levels (suc n) = Level × Levels n

private
  variable
    ls : Levels n

max-level : Levels n → Level
max-level {zero} _ = ℓzero
max-level {suc n} (x , xs) =
  x ℓ⊔ max-level xs

Types : ∀ n → (ls : Levels n) → Type (ℓsuc (max-level ls))
Types zero ls = ⊤
Types (suc n) (l , ls) = Type l × Types n ls

⦅_⦆⁺ :  Types (suc n) ls →
        Type (max-level ls)
⦅_⦆⁺ {n = zero } (X , Xs) = X
⦅_⦆⁺ {n = suc n} (X , Xs) = X × ⦅ Xs ⦆⁺

⦅_⦆ :  Types n ls →
       Type (max-level ls)
⦅_⦆ {n = zero} _ = ⊤
⦅_⦆ {n = suc n} = ⦅_⦆⁺ {n = n}

map-types : (fn : ∀ {ℓ} → Type ℓ → Type ℓ) → ∀ {n ls} → Types n ls → Types n ls
map-types fn {zero} xs = xs
map-types fn {suc n} (x , xs) = fn x , map-types fn xs

data ArgForm : Type₀ where expl impl inst : ArgForm

infixr 0 _[_]→_
_[_]→_ : Type a → ArgForm → Type b → Type (a ℓ⊔ b)
A [ expl  ]→ B =         A    → B
A [ impl  ]→ B = {  _ :  A }  → B
A [ inst  ]→ B = ⦃  _ :  A ⦄  → B

[_$] : ∀ form → (A [ form ]→ B) ⇔ (A → B)
[ expl $] .fun f = f
[ impl $] .fun f x = f {x}
[ inst $] .fun f x = f ⦃ x ⦄
[ expl $] .inv f = f
[ impl $] .inv f {x} = f x
[ inst $] .inv f ⦃ x ⦄ = f x
[ expl $] .leftInv f = refl
[ impl $] .leftInv f = refl
[ inst $] .leftInv f = refl
[ expl $] .rightInv f = refl
[ impl $] .rightInv f = refl
[ inst $] .rightInv f = refl

infixr 0 pi-arr
pi-arr : (A : Type a) → ArgForm → (A → Type b) → Type (a ℓ⊔ b)
pi-arr A expl B = (x : A) → B x
pi-arr A impl B = {x : A} → B x
pi-arr A inst B = ⦃ x : A ⦄ → B x

syntax pi-arr a f (λ x → b ) = x ⦂ a Π[ f ]→ b
Π[_$] : ∀ {B : A → Type b} fr → (x ⦂ A Π[ fr ]→ B x) ⇔ ((x : A) → B x)
Π[ expl $] .fun f = f
Π[ impl $] .fun f x = f {x}
Π[ inst $] .fun f x = f ⦃ x ⦄
Π[ expl $] .inv f x = f x
Π[ impl $] .inv f {x} = f x
Π[ inst $] .inv f ⦃ x ⦄ = f x
Π[ expl $] .leftInv f = refl
Π[ impl $] .leftInv f = refl
Π[ inst $] .leftInv f = refl
Π[ expl $] .rightInv f = refl
Π[ impl $] .rightInv f = refl
Π[ inst $] .rightInv f = refl

infixr 0 ⦅_⦆[_]→_
⦅_⦆[_]→_ : Types n ls → ArgForm → Type ℓ → Type (max-level ls ℓ⊔ ℓ)
⦅_⦆[_]→_ {n = zero}  Xs fr Y = Y
⦅_⦆[_]→_ {n = suc n} (X , Xs) fr Y = X [ fr ]→ ⦅ Xs ⦆[ fr ]→ Y


infixr 0 pi-arrs-plus
pi-arrs-plus :
  (Xs : Types (suc n) ls) →
  ArgForm →
  (y : ⦅ Xs ⦆⁺ → Type ℓ) →
  Type (max-level ls ℓ⊔ ℓ)
pi-arrs-plus {n = zero   } (X , Xs) fr Y = x ⦂ X Π[ fr ]→ Y x
pi-arrs-plus {n = suc n  } (X , Xs) fr Y =
  x ⦂ X Π[ fr ]→ xs ⦂⦅ Xs ⦆⁺Π[ fr ]→ Y (x , xs)

syntax pi-arrs-plus Xs fr (λ xs → Y) = xs ⦂⦅ Xs ⦆⁺Π[ fr ]→ Y

pi-arrs : ∀ {n ls ℓ} → (Xs : Types n ls) → ArgForm → (y : ⦅ Xs ⦆ → Type ℓ) → Type (max-level ls ℓ⊔ ℓ)
pi-arrs {n = zero} xs fr Y = Y tt
pi-arrs {n = suc n} = pi-arrs-plus
syntax pi-arrs Xs fr (λ xs → Y) = xs ⦂⦅ Xs ⦆Π[ fr ]→ Y

[_^_$]⁺↓ : ∀ n {ls ℓ} f {Xs : Types (suc n) ls} {y : Type ℓ} → (⦅ Xs ⦆⁺ → y) → ⦅ Xs ⦆[ f ]→ y
[ zero  ^ fr $]⁺↓ f = [ fr $] .inv f
[ suc n ^ fr $]⁺↓ f = [ fr $] .inv ([ n ^ fr $]⁺↓ ∘ (f ∘_) ∘ _,_)

[_^_$]↓ : ∀ n {ls ℓ} f {xs : Types n ls} {y : Type ℓ} → (⦅ xs ⦆ → y) → ⦅ xs ⦆[ f ]→ y
[ zero  ^ fr $]↓ f = f tt
[ suc n ^ fr $]↓ f = [ n ^ fr $]⁺↓ f

[_^_$]⁺↑ : ∀ n {ls ℓ} f {xs : Types (suc n) ls} {y : Type ℓ} → (⦅ xs ⦆[ f ]→ y) → (⦅ xs ⦆⁺ → y)
[ zero  ^ fr $]⁺↑ f = [ fr $] .fun f
[ suc n ^ fr $]⁺↑ f = uncurry ([ n ^ fr $]⁺↑ ∘ [ fr $] .fun f)

[_^_$]↑ : ∀ n {ls ℓ} f {xs : Types n ls} {y : Type ℓ} → (⦅ xs ⦆[ f ]→ y) → (⦅ xs ⦆ → y)
[ zero ^ fr  $]↑ f _ = f
[ suc n ^ fr $]↑ f = [ n ^ fr $]⁺↑ f

leftInvCurry⁺ : ∀ n {ls ℓ} fr {Xs : Types (suc n) ls} {Y : Type ℓ}
              → (f : ⦅ Xs ⦆[ fr ]→ Y ) → [ n ^ fr $]⁺↓ ([ n ^ fr $]⁺↑ f) ≡ f
leftInvCurry⁺ zero fr f = [ fr $] .leftInv f
leftInvCurry⁺ (suc n) fr f =
  [ fr $] .inv ([ n ^ fr $]⁺↓ ∘ [ n ^ fr $]⁺↑ ∘ [ fr $] .fun f) ≡⟨ cong (λ r → [ fr $] .inv (r ∘ [ fr $] .fun f)) (funExt (leftInvCurry⁺ n fr)) ⟩
  [ fr $] .inv ([ fr $] .fun f) ≡⟨ [ fr $] .leftInv f ⟩
  f ∎

leftInvCurry : ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : Type ℓ}
             → (f : ⦅ Xs ⦆[ fr ]→ Y ) → [ n ^ fr $]↓ ([ n ^ fr $]↑ f) ≡ f
leftInvCurry zero fr f = refl
leftInvCurry (suc n) fr f = leftInvCurry⁺ n fr f

rightInvCurry⁺ : ∀ n {ls ℓ} fr {Xs : Types (suc n) ls} {Y : Type ℓ} (f : ⦅ Xs ⦆ → Y)
              → [ n ^ fr $]⁺↑ ([ n ^ fr $]⁺↓ f) ≡ f
rightInvCurry⁺ zero fr f = [ fr $] .rightInv f
rightInvCurry⁺ (suc n) fr f =
  uncurry ([ n ^ fr $]⁺↑ ∘ [ fr $] .fun ([ fr $] .inv ([ n ^ fr $]⁺↓ ∘ ((f ∘_) ∘ _,_)))) ≡⟨ cong (λ h → uncurry ([ n ^ fr $]⁺↑ ∘ h)) ([ fr $] .rightInv _) ⟩
  uncurry ([ n ^ fr $]⁺↑ ∘ [ n ^ fr $]⁺↓ ∘ ((f ∘_) ∘ _,_)) ≡⟨ cong (λ r → uncurry (r ∘ ((f ∘_) ∘ _,_))) (funExt (rightInvCurry⁺ n fr)) ⟩
  f ∎

rightInvCurry : ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : Type ℓ} (f : ⦅ Xs ⦆ → Y)
              → [ n ^ fr $]↑ ([ n ^ fr $]↓ f) ≡ f
rightInvCurry zero fr f = refl
rightInvCurry (suc n) fr f = rightInvCurry⁺ n fr f

[_^_$] : ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : Type ℓ}
       → (⦅ Xs ⦆[ fr ]→ Y) ⇔ (⦅ Xs ⦆ → Y)
[ n ^ fr $] .fun = [ n ^ fr $]↑
[ n ^ fr $] .inv = [ n ^ fr $]↓
[ n ^ fr $] .leftInv  = leftInvCurry n fr
[ n ^ fr $] .rightInv = rightInvCurry n fr

↓Π[_^_$]⁺ : ∀ n {ls ℓ} fr {Xs : Types (suc n) ls} {Y : ⦅ Xs ⦆ → Type ℓ} → ((xs : ⦅ Xs ⦆) → Y xs) → xs ⦂⦅ Xs ⦆⁺Π[ fr ]→ Y xs
↓Π[ zero ^ fr  $]⁺ f = Π[ fr $] .inv f
↓Π[ suc n ^ fr $]⁺ f = Π[ fr $] .inv (↓Π[ n ^ fr $]⁺ ∘ (f ∘_) ∘ _,_)

↓Π[_^_$] : ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : ⦅ Xs ⦆ → Type ℓ} → ((xs : ⦅ Xs ⦆) → Y xs) → xs ⦂⦅ Xs ⦆Π[ fr ]→ Y xs
↓Π[ zero ^ fr $] f = f tt
↓Π[ suc n ^ fr $] f = ↓Π[ n ^ fr $]⁺ f

↑Π[_^_$]⁺ : ∀ n {ls ℓ} fr {Xs : Types (suc n) ls} {Y : ⦅ Xs ⦆ → Type ℓ} → (xs ⦂⦅ Xs ⦆⁺Π[ fr ]→ Y xs) → ((xs : ⦅ Xs ⦆) → Y xs)
↑Π[ zero ^ fr  $]⁺ f = Π[ fr $] .fun f
↑Π[ suc n ^ fr $]⁺ f = uncurry (↑Π[ n ^ fr $]⁺ ∘ Π[ fr $] .fun f)

↑Π[_^_$] : ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : ⦅ Xs ⦆ → Type ℓ} → (xs ⦂⦅ Xs ⦆Π[ fr ]→ Y xs) → ((xs : ⦅ Xs ⦆) → Y xs)
↑Π[ zero ^ fr  $] f _ = f
↑Π[ suc n ^ fr $] f = ↑Π[ n ^ fr $]⁺ f

leftInvCurryΠ⁺ : ∀ n {ls ℓ} fr {Xs : Types (suc n) ls} {Y : ⦅ Xs ⦆ → Type ℓ}
              → (f : xs ⦂⦅ Xs ⦆⁺Π[ fr ]→ Y xs) → ↓Π[ n ^ fr $]⁺ (↑Π[ n ^ fr $]⁺ f) ≡ f
leftInvCurryΠ⁺ zero fr f = Π[ fr $] .leftInv f
leftInvCurryΠ⁺ (suc n) fr f =
  Π[ fr $] .inv (↓Π[ n ^ fr $]⁺ ∘ ↑Π[ n ^ fr $]⁺ ∘ Π[ fr $] .fun f)  ≡⟨ cong (Π[ fr $] .inv ∘ flip _∘_ (Π[ fr $] .fun f)) (λ i x → leftInvCurryΠ⁺ n fr x i) ⟩
  Π[ fr $] .inv (Π[ fr $] .fun f) ≡⟨ Π[ fr $] .leftInv f ⟩
  f ∎

leftInvCurryΠ : ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : ⦅ Xs ⦆ → Type ℓ}
              → (f : xs ⦂⦅ Xs ⦆Π[ fr ]→ Y xs) → ↓Π[ n ^ fr $] (↑Π[ n ^ fr $] f) ≡ f
leftInvCurryΠ zero fr f = refl
leftInvCurryΠ (suc n) fr f = leftInvCurryΠ⁺ n fr f

rightInvCurryΠ⁺ : ∀ n {ls ℓ} fr {Xs : Types (suc n) ls} {Y : ⦅ Xs ⦆ → Type ℓ} (f : (xs : ⦅ Xs ⦆) → Y xs)
               → ↑Π[ n ^ fr $]⁺ (↓Π[ n ^ fr $]⁺ f) ≡ f
rightInvCurryΠ⁺ zero fr f = Π[ fr $] .rightInv f
rightInvCurryΠ⁺ (suc n) fr f =
  uncurry (↑Π[ n ^ fr $]⁺ ∘ (Π[ fr $] .fun (Π[ fr $] .inv (↓Π[ n ^ fr $]⁺ ∘ (f ∘_) ∘ _,_)))) ≡⟨ cong (λ h → uncurry (↑Π[ n ^ fr $]⁺ ∘ h)) (Π[ fr $] .rightInv _) ⟩
  uncurry (↑Π[ n ^ fr $]⁺ ∘ ↓Π[ n ^ fr $]⁺ ∘ (f ∘_) ∘ _,_) ≡⟨ cong (uncurry ∘ flip _∘_ ((f ∘_) ∘ _,_)) (λ i x → rightInvCurryΠ⁺ n fr x i) ⟩
  f ∎

rightInvCurryΠ : ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : ⦅ Xs ⦆ → Type ℓ} (f : (xs : ⦅ Xs ⦆) → Y xs)
               → ↑Π[ n ^ fr $] (↓Π[ n ^ fr $] f) ≡ f
rightInvCurryΠ zero fr f = refl
rightInvCurryΠ (suc n) fr f = rightInvCurryΠ⁺ n fr f

Π[_^_$] :  ∀ n {ls ℓ} fr {Xs : Types n ls} {Y : ⦅ Xs ⦆ → Type ℓ} →
           (xs ⦂⦅ Xs ⦆Π[ fr ]→ Y xs) ⇔ ((xs : ⦅ Xs ⦆) → Y xs)
Π[ n ^ fr $] .fun = ↑Π[ n ^ fr $]
Π[ n ^ fr $] .inv = ↓Π[ n ^ fr $]
Π[ n ^ fr $] .leftInv  = leftInvCurryΠ n fr
Π[ n ^ fr $] .rightInv = rightInvCurryΠ n fr
