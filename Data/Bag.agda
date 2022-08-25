{-# OPTIONS --cubical --safe #-}

module Data.Bag where

open import Prelude
open import Algebra
open import Path.Reasoning

infixr 5 _∷_
data ⟅_⟆ (A : Type a) : Type a where
  []     : ⟅ A ⟆
  _∷_    : A → ⟅ A ⟆ → ⟅ A ⟆
  com    : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc  : isSet ⟅ A ⟆

record Elim {a ℓ}
             (A : Type a)
             (P : ⟅ A ⟆ → Type ℓ)
             : Type (a ℓ⊔ ℓ) where
  constructor elim
  field
    ⟅_⟆-set : ∀ {xs} → isSet (P xs)
    ⟅_⟆[] : P []
    ⟅_⟆_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ⟅_⟆[]; f = ⟅_⟆_∷_⟨_⟩
  field
    ⟅_⟆-com : (∀ x y xs pxs →
      PathP  (λ i → P (com x y xs i))
             (f x (y ∷ xs) (f y xs pxs))
             (f y (x ∷ xs) (f x xs pxs)))
  ⟅_⟆⇓ : (xs : ⟅ A ⟆) → P xs
  ⟅ [] ⟆⇓ = z
  ⟅ x ∷ xs ⟆⇓ = f x xs ⟅ xs ⟆⇓
  ⟅ com x y xs i ⟆⇓ = ⟅_⟆-com x y xs ⟅ xs ⟆⇓ i
  ⟅ trunc xs ys x y i j ⟆⇓ =
    isOfHLevel→isOfHLevelDep 2
      (λ xs → ⟅_⟆-set {xs})
      ⟅ xs ⟆⇓ ⟅ ys ⟆⇓
      (cong ⟅_⟆⇓ x) (cong ⟅_⟆⇓ y)
      (trunc xs ys x y)
      i j

open Elim


infixr 0 elim-syntax
elim-syntax  : ∀ {a ℓ}
             → (A : Type a)
             → (⟅ A ⟆ → Type ℓ)
             → Type (a ℓ⊔ ℓ)
elim-syntax = Elim

syntax elim-syntax A (λ xs → Pxs) = xs ⦂⟅ A ⟆→ Pxs

record ElimProp {a ℓ} (A : Type a) (P : ⟅ A ⟆ → Type ℓ) : Type (a ℓ⊔ ℓ) where
  constructor elim-prop
  field
    ⟦_⟧-prop : ∀ {xs} → isProp (P xs)
    ⟦_⟧[] : P []
    ⟦_⟧_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ⟦_⟧[]; f = ⟦_⟧_∷_⟨_⟩
  ⟦_⟧⇑ = elim
          (isProp→isSet ⟦_⟧-prop)
          z f
          (λ x y xs pxs → toPathP (⟦_⟧-prop (transp (λ i → P (com x y xs i)) i0
            (f x (y ∷ xs) (f y xs pxs))) (f y (x ∷ xs) (f x xs pxs))))
  ⟦_⟧⇓ = ⟅ ⟦_⟧⇑ ⟆⇓

open ElimProp

infixr 0 elim-prop-syntax
elim-prop-syntax : ∀ {a ℓ} → (A : Type a) → (⟅ A ⟆ → Type ℓ) → Type (a ℓ⊔ ℓ)
elim-prop-syntax = ElimProp

syntax elim-prop-syntax A (λ xs → Pxs) = xs ⦂⟅ A ⟆→∥ Pxs ∥

record [⟅_⟆→_] {a b} (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor rec
  field
    [_]-set  : isSet B
    [_]_∷_ : A → B → B
    [_][]    : B
  private f = [_]_∷_; z = [_][]
  field
    [_]-com : ∀ x y xs → f x (f y xs) ≡ f y (f x xs)
  [_]⇑ = elim [_]-set z (λ x _ → f x) (λ x y _ → [_]-com x y)
  [_]↓ = ⟅ [_]⇑ ⟆⇓
open [⟅_⟆→_]

infixr 5 _∪_
_∪_ : ⟅ A ⟆ → ⟅ A ⟆ → ⟅ A ⟆
_∪_ = λ xs ys → [ ys ∪′ ]↓ xs
  where
  _∪′ : ⟅ A ⟆ → [⟅ A ⟆→ ⟅ A ⟆ ]
  [ ys ∪′ ]-set = trunc
  [ ys ∪′ ] x ∷ xs = x ∷ xs
  [ ys ∪′ ][] = ys
  [ ys ∪′ ]-com = com

∪-assoc : (xs ys zs : ⟅ A ⟆) →
  (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs)
∪-assoc = λ xs ys zs → ⟦ ∪-assoc′ ys zs ⟧⇓ xs
  where
  ∪-assoc′ : ∀ ys zs →
    xs ⦂⟅ A ⟆→∥ (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs) ∥
  ⟦ ∪-assoc′ ys zs ⟧-prop = trunc _ _
  ⟦ ∪-assoc′ ys zs ⟧[] = refl
  ⟦ ∪-assoc′ ys zs ⟧ x ∷ xs ⟨ P ⟩ = cong (x ∷_) P

∪-cons  : ∀ (x : A) xs ys
        → (x ∷ xs) ∪ ys ≡ xs ∪ (x ∷ ys)
∪-cons = λ x xs ys → ⟦ ∪-cons′ x ys ⟧⇓ xs
  where
  ∪-cons′ : ∀ x ys →
    xs ⦂⟅ A ⟆→∥ (x ∷ xs) ∪ ys ≡ xs ∪ (x ∷ ys) ∥
  ⟦ ∪-cons′ x ys ⟧-prop = trunc _ _
  ⟦ ∪-cons′ x ys ⟧[] = refl
  ⟦ ∪-cons′ x ys ⟧ y ∷ xs ⟨ P ⟩ = cong (_∪ ys) (com x y xs) ; cong (y ∷_) P

∪-idʳ : (xs : ⟅ A ⟆) → xs ∪ [] ≡ xs
∪-idʳ = ⟦ ∪-idʳ′ ⟧⇓
  where
  ∪-idʳ′ : xs ⦂⟅ A ⟆→∥ xs ∪ [] ≡ xs ∥
  ⟦ ∪-idʳ′ ⟧-prop = trunc _ _
  ⟦ ∪-idʳ′ ⟧[] = refl
  ⟦ ∪-idʳ′ ⟧ x ∷ xs ⟨ P ⟩ = cong (x ∷_) P

∪-comm : (xs ys : ⟅ A ⟆) → xs ∪ ys ≡ ys ∪ xs
∪-comm {A = A} = λ xs ys → ⟦ ∪-comm′ ys ⟧⇓ xs
  where
  ∪-comm′ : (ys : ⟅ A ⟆) →
    xs ⦂⟅ A ⟆→∥ xs ∪ ys ≡ ys ∪ xs ∥
  ⟦ ∪-comm′ ys ⟧-prop = trunc _ _
  ⟦ ∪-comm′ ys ⟧[] = sym (∪-idʳ ys)
  ⟦ ∪-comm′ ys ⟧ x ∷ xs ⟨ P ⟩ =
    (x ∷ xs) ∪ ys ≡⟨ cong (x ∷_) P ⟩
    (x ∷ ys) ∪ xs ≡⟨ ∪-cons x ys xs ⟩
    ys ∪ x ∷ xs ∎

⟅⟆-commutative-monoid : ∀ {a} (A : Type a) → CommutativeMonoid ⟅ A ⟆
Monoid._∙_ (CommutativeMonoid.monoid (⟅⟆-commutative-monoid A)) = _∪_
Monoid.ε (CommutativeMonoid.monoid (⟅⟆-commutative-monoid A)) = []
Monoid.assoc (CommutativeMonoid.monoid (⟅⟆-commutative-monoid A)) = ∪-assoc
Monoid.ε∙ (CommutativeMonoid.monoid (⟅⟆-commutative-monoid A)) _ = refl
Monoid.∙ε (CommutativeMonoid.monoid (⟅⟆-commutative-monoid A)) = ∪-idʳ
CommutativeMonoid.comm (⟅⟆-commutative-monoid A) = ∪-comm

module _ {ℓ} {𝑆 : Type ℓ} (mon : CommutativeMonoid 𝑆) (sIsSet : isSet 𝑆) where
  open CommutativeMonoid mon
  ⟦_⟧ : (A → 𝑆) → ⟅ A ⟆ → 𝑆
  ⟦_⟧ = λ h → [ ⟦ h ⟧′ ]↓
    where
    ⟦_⟧′ : (A → 𝑆) → [⟅ A ⟆→ 𝑆 ]
    [ ⟦ h ⟧′ ] x ∷ xs = h x ∙ xs
    [ ⟦ h ⟧′ ][] = ε
    [ ⟦ h ⟧′ ]-com x y xs =
      h x ∙ (h y ∙ xs)
        ≡˘⟨ assoc _ _ _ ⟩
      (h x ∙ h y) ∙ xs
        ≡⟨ cong (_∙ xs) (comm _ _) ⟩
      (h y ∙ h x) ∙ xs
        ≡⟨ assoc _ _ _ ⟩
      h y ∙ (h x ∙ xs) ∎
    [ ⟦ h ⟧′ ]-set = sIsSet

record ⟦_≡_⟧ {a b} {A : Type a} {B : Type b}
            (h : ⟅ A ⟆ → B)
            (xf : [⟅ A ⟆→ B ])
            : Type (a ℓ⊔ b) where
  constructor elim-univ
  field
    ⟦_≡⟧_∷_ : ∀ x xs → h (x ∷ xs) ≡ [ xf ] x ∷ h xs
    ⟦_≡⟧[] : h [] ≡ [ xf ][]
  ⟦_≡⟧⇓ : ∀ xs → h xs ≡ [ xf ]↓ xs
  ⟦_≡⟧⇓ = ⟦ ≡⇓′ ⟧⇓
    where
    ≡⇓′ : xs ⦂⟅ A ⟆→∥ h xs ≡ [ xf ]↓ xs ∥
    ⟦ ≡⇓′ ⟧-prop = [ xf ]-set _ _
    ⟦ ≡⇓′ ⟧[] = ⟦_≡⟧[]
    ⟦ ≡⇓′ ⟧ x ∷ xs ⟨ P ⟩ = ⟦_≡⟧_∷_ x _ ; cong ([ xf ] x ∷_) P
open ⟦_≡_⟧

record ⟦_⊚_≡_⟧ {a b c} {A : Type a} {B : Type b} {C : Type c}
               (h : B → C)
               (xf : [⟅ A ⟆→ B ])
               (yf : [⟅ A ⟆→ C ])
               : Type (a ℓ⊔ b ℓ⊔ c)
    where
  constructor elim-fuse
  field
    ⟦_∘≡⟧_∷_ : ∀ x xs → h ([ xf ] x ∷ xs) ≡ [ yf ] x ∷ h xs
    ⟦_∘≡⟧[] : h [ xf ][] ≡ [ yf ][]
  ⟦_∘≡⟧⇓ : ∀ xs → h ([ xf ]↓ xs) ≡ [ yf ]↓ xs
  ⟦_∘≡⟧⇓ = ⟦ ≡⇓′ ⟧⇓
    where
    ≡⇓′ : xs ⦂⟅ A ⟆→∥ h ([ xf ]↓ xs) ≡ [ yf ]↓ xs ∥
    ⟦ ≡⇓′ ⟧-prop = [ yf ]-set _ _
    ⟦ ≡⇓′ ⟧[] = ⟦_∘≡⟧[]
    ⟦ ≡⇓′ ⟧ x ∷ xs ⟨ P ⟩ = ⟦_∘≡⟧_∷_ x _ ; cong ([ yf ] x ∷_) P
open ⟦_⊚_≡_⟧

map-alg : (A → B) → [⟅ A ⟆→ ⟅ B ⟆ ]
[ map-alg f ]-set = trunc
[ map-alg f ][] = []
[ map-alg f ] x ∷ xs = f x ∷ xs
[ map-alg f ]-com x y = com (f x) (f y)

map : (A → B) → ⟅ A ⟆ → ⟅ B ⟆
map f = [ map-alg f ]↓

[_]∘_ : [⟅ B ⟆→ C ] → (A → B) → [⟅ A ⟆→ C ]
[ [ g ]∘ f ]-set      = [ g ]-set
[ [ g ]∘ f ][]        = [ g ][]
[ [ g ]∘ f ] x ∷ xs   = [ g ] f x ∷ xs
[ [ g ]∘ f ]-com x y  = [ g ]-com (f x) (f y)

map-fuse  : ∀ (g : [⟅ B ⟆→ C ]) (f : A → B)
          → [ g ]↓ ∘ map f ≡ [ [ g ]∘ f ]↓
map-fuse g f = funExt ⟦ map-fuse′ g f ∘≡⟧⇓
  where
  map-fuse′  : (g : [⟅ B ⟆→ C ]) (f : A → B)
             → ⟦ [ g ]↓ ⊚ map-alg f ≡ [ g ]∘ f ⟧
  ⟦ map-fuse′ g f ∘≡⟧ x ∷ xs = refl
  ⟦ map-fuse′ g f ∘≡⟧[] = refl

bind : ⟅ A ⟆ → (A → ⟅ B ⟆) → ⟅ B ⟆
bind xs f = ⟦ ⟅⟆-commutative-monoid _ ⟧ trunc f xs
