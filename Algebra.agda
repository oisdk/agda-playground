{-# OPTIONS --cubical --safe #-}
module Algebra where

open import Prelude

module _ {a} {A : Type a} (_∙_ : A → A → A) where
  Associative : Type a
  Associative = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  Commutative : Type _
  Commutative = ∀ x y → x ∙ y ≡ y ∙ x

  Idempotent : Type _
  Idempotent = ∀ x → x ∙ x ≡ x

module _ {a b} {A : Type a} {B : Type b} where
  Identityˡ : (A → B → B) → A → Type _
  Identityˡ _∙_ x = ∀ y → x ∙ y ≡ y

  Zeroˡ : (A → B → A) → A → Type _
  Zeroˡ _∙_ x = ∀ y → x ∙ y ≡ x

  Zeroʳ : (A → B → B) → B → Type _
  Zeroʳ _∙_ x = ∀ y → y ∙ x ≡ x

  Identityʳ : (A → B → A) → B → Type _
  Identityʳ _∙_ x = ∀ y → y ∙ x ≡ y

  _Distributesʳ_ : (A → B → B) → (B → B → B) → Type _
  _⊗_ Distributesʳ _⊕_ = ∀ x y z → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)

  _Distributesˡ_ : (B → A → B) → (B → B → B) → Type _
  _⊗_ Distributesˡ _⊕_ = ∀ x y z → (x ⊕ y) ⊗ z ≡ (x ⊗ z) ⊕ (y ⊗ z)

record  Semigroup ℓ : Type (ℓsuc ℓ) where
  infixl 6 _∙_
  field
    𝑆      : Type ℓ
    _∙_    : 𝑆 → 𝑆 → 𝑆
    assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record  Monoid ℓ : Type (ℓsuc ℓ) where
  infixl 6 _∙_
  field
    𝑆      : Type ℓ
    _∙_    : 𝑆 → 𝑆 → 𝑆
    ε      : 𝑆
    assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    ε∙     : ∀ x → ε ∙ x ≡ x
    ∙ε     : ∀ x → x ∙ ε ≡ x

  semigroup : Semigroup ℓ
  semigroup = record
    { 𝑆 = 𝑆; _∙_ = _∙_; assoc = assoc }

record MonoidHomomorphism_⟶_
         {ℓ₁ ℓ₂}
         (from : Monoid ℓ₁)
         (to : Monoid ℓ₂)
       : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  open Monoid from
  open Monoid to
    renaming ( 𝑆 to 𝑅
             ; _∙_ to _⊙_
             ; ε to ⓔ
             )
  field
    f : 𝑆 → 𝑅
    ∙-homo : ∀ x y → f (x ∙ y) ≡ f x ⊙ f y
    ε-homo : f ε ≡ ⓔ

record Group ℓ : Type (ℓsuc ℓ) where
  field
    monoid : Monoid ℓ
  open Monoid monoid public
  field
    inv : 𝑆 → 𝑆
    ∙⁻ : ∀ x → x ∙ inv x ≡ ε
    ⁻∙ : ∀ x → inv x ∙ x ≡ ε

record CommutativeMonoid ℓ : Type (ℓsuc ℓ) where
  field
    monoid : Monoid ℓ
  open Monoid monoid public
  field
    comm : Commutative _∙_

record Semilattice ℓ : Type (ℓsuc ℓ) where
  field
    commutativeMonoid : CommutativeMonoid ℓ
  open CommutativeMonoid commutativeMonoid public
  field
    idem : Idempotent _∙_

record NearSemiring ℓ : Type (ℓsuc ℓ) where
  infixl 6 _+_
  infixl 7 _*_
  field
    𝑅 : Type ℓ
    _+_ : 𝑅 → 𝑅 → 𝑅
    _*_ : 𝑅 → 𝑅 → 𝑅
    1# : 𝑅
    0# : 𝑅
    +-assoc : Associative _+_
    *-assoc : Associative _*_
    0+ : Identityˡ _+_ 0#
    +0 : Identityʳ _+_ 0#
    1* : Identityˡ _*_ 1#
    *1 : Identityʳ _*_ 1#
    0* : Zeroˡ _*_ 0#
    ⟨+⟩* : _*_ Distributesˡ _+_

record Semiring ℓ : Type (ℓsuc ℓ) where
  field
    nearSemiring : NearSemiring ℓ
  open NearSemiring nearSemiring public
  field
    +-comm : Commutative _+_
    *0 : Zeroʳ _*_ 0#
    *⟨+⟩ : _*_ Distributesʳ _+_

record IdempotentSemiring ℓ : Type (ℓsuc ℓ) where
  field
    semiring : Semiring ℓ
  open Semiring semiring public
  field
    +-idem : Idempotent _+_


record CommutativeSemiring ℓ : Type (ℓsuc ℓ) where
  field
    semiring : Semiring ℓ
  open Semiring semiring public
  field
    *-comm : Commutative _*_

record LeftSemimodule ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    semiring : Semiring ℓ₁
  open Semiring semiring public
  field
    semimodule : CommutativeMonoid ℓ₂
  open CommutativeMonoid semimodule renaming (_∙_ to _∪_) public
    renaming (𝑆 to 𝑉
             ; assoc to ∪-assoc
             ; ε∙ to ∅∪
             ; ∙ε to ∪∅
             ; ε to ∅
             )
  infixr 7 _⋊_
  field
    _⋊_ : 𝑅 → 𝑉 → 𝑉
    ⟨*⟩⋊ : ∀ x y z → (x * y) ⋊ z ≡ x ⋊ (y ⋊ z)
    ⟨+⟩⋊ : ∀ x y z → (x + y) ⋊ z ≡ (x ⋊ z) ∪ (y ⋊ z)
    ⋊⟨∪⟩ : _⋊_ Distributesʳ _∪_
    1⋊ : Identityˡ _⋊_ 1#
    0⋊ : ∀ x → 0# ⋊ x ≡ ∅

record StarSemiring ℓ : Type (ℓsuc ℓ) where
  field
    semiring : Semiring ℓ
  open Semiring semiring public
  field
    _⋆ : 𝑅 → 𝑅
    star-iterʳ : ∀ x → x ⋆ ≡ 1# + x * x ⋆
    star-iterˡ : ∀ x → x ⋆ ≡ 1# + x ⋆ * x
  _⁺ : 𝑅 → 𝑅
  x ⁺ = x * x ⋆

record Functor ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    𝐹   : Type ℓ₁ → Type ℓ₂
    map : (A → B) → 𝐹 A → 𝐹 B
    map-id : map (id {ℓ₁} {A}) ≡ id
    map-comp : (f : B → C) → (g : A → B) → map (f ∘ g) ≡ map f ∘ map g

record Applicative ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    functor : Functor ℓ₁ ℓ₂
  open Functor functor public
  infixl 5 _<*>_
  field
    pure : A → 𝐹 A
    _<*>_ : 𝐹 (A → B) → 𝐹 A → 𝐹 B
    map-ap : (f : A → B) → map f ≡ pure f <*>_
    pure-homo : (f : A → B) → (x : A) → map f (pure x) ≡ pure (f x)
    <*>-interchange : (u : 𝐹 (A → B)) → (y : A) → u <*> pure y ≡ map (_$ y) u
    <*>-comp : (u : 𝐹 (B → C)) → (v : 𝐹 (A → B)) → (w : 𝐹 A) → pure _∘′_ <*> u <*> v <*> w ≡ u <*> (v <*> w)

record Monad ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    applicative : Applicative ℓ₁ ℓ₂
  open Applicative applicative public
  infixl 1 _>>=_
  field
    _>>=_ : 𝐹 A → (A → 𝐹 B) → 𝐹 B
    >>=-idˡ : (f : A → 𝐹 B) → (x : A) → (pure x >>= f) ≡ f x
    >>=-idʳ : (x : 𝐹 A) → (x >>= pure) ≡ x
    >>=-assoc : (xs : 𝐹 A) (f : A → 𝐹 B) (g : B → 𝐹 C) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))
  return : A → 𝐹 A
  return = pure

record Alternative ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    applicative : Applicative ℓ₁ ℓ₂
  open Applicative applicative public
  field
    0# : 𝐹 A
    _<|>_ : 𝐹 A → 𝐹 A → 𝐹 A
    <|>-idˡ : (x : 𝐹 A) → 0# <|> x ≡ x
    <|>-idʳ : (x : 𝐹 A) → x <|> 0# ≡ x
    0-annˡ : (x : 𝐹 A) → 0# <*> x ≡ 0# {B}
    <|>-distrib : (x y : 𝐹 (A → B)) → (z : 𝐹 A) → (x <|> y) <*> z ≡ (x <*> z) <|> (y <*> z)

record MonadPlus ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    monad : Monad ℓ₁ ℓ₂
  open Monad monad public
  field
    0# : 𝐹 A
    _<|>_ : 𝐹 A → 𝐹 A → 𝐹 A
    <|>-idˡ : (x : 𝐹 A) → 0# <|> x ≡ x
    <|>-idʳ : (x : 𝐹 A) → x <|> 0# ≡ x
    0-annˡ : (x : A → 𝐹 B) → (0# >>= x) ≡ 0#
    <|>-distrib : (x y : 𝐹 A) → (z : A → 𝐹 B) → ((x <|> y) >>= z) ≡ (x >>= z) <|> (y >>= z)

Endo : Type a → Type a
Endo A = A → A

endoMonoid : ∀ {a} → Type a → Monoid a
endoMonoid A .Monoid.𝑆 = Endo A
endoMonoid A .Monoid.ε x = x
endoMonoid A .Monoid._∙_ f g x = f (g x)
endoMonoid A .Monoid.assoc _ _ _ = refl
endoMonoid A .Monoid.ε∙ _ = refl
endoMonoid A .Monoid.∙ε _ = refl

record Foldable ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    𝐹 : Type ℓ₁ → Type ℓ₂
  open Monoid ⦃ ... ⦄
  field
    foldMap : {A : Type ℓ₁} ⦃ _ : Monoid ℓ₁ ⦄ → (A → 𝑆) → 𝐹 A → 𝑆
  foldr : {A B : Type ℓ₁} → (A → B → B) → B → 𝐹 A → B
  foldr f b xs = foldMap ⦃ endoMonoid _ ⦄ f xs b
