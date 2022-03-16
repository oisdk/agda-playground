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

Cancellableˡ : (A → B → C) → A → Type _
Cancellableˡ _⊗_ c = ∀ x y → c ⊗ x ≡ c ⊗ y → x ≡ y

Cancellableʳ : (A → B → C) → B → Type _
Cancellableʳ _⊗_ c = ∀ x y → x ⊗ c ≡ y ⊗ c → x ≡ y

Cancellativeˡ : (A → B → C) → Type _
Cancellativeˡ _⊗_ = ∀ c → Cancellableˡ _⊗_ c

Cancellativeʳ : (A → B → C) → Type _
Cancellativeʳ _⊗_ = ∀ c → Cancellableʳ _⊗_ c

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
    -_ : 𝑆 → 𝑆
    ∙⁻ : ∀ x → x ∙ - x ≡ ε
    ⁻∙ : ∀ x → - x ∙ x ≡ ε

  open import Path.Reasoning

  cancelˡ : Cancellativeˡ _∙_
  cancelˡ x y z p =
    y ≡˘⟨ ε∙ y ⟩
    ε ∙ y ≡˘⟨ cong (_∙ y) (⁻∙ x) ⟩
    (- x ∙ x) ∙ y ≡⟨ assoc (- x) x y ⟩
    - x ∙ (x ∙ y) ≡⟨ cong (- x ∙_) p ⟩
    - x ∙ (x ∙ z) ≡˘⟨ assoc (- x) x z ⟩
    (- x ∙ x) ∙ z ≡⟨ cong (_∙ z) (⁻∙ x) ⟩
    ε ∙ z ≡⟨ ε∙ z ⟩
    z ∎

  cancelʳ : Cancellativeʳ _∙_
  cancelʳ x y z p =
    y ≡˘⟨ ∙ε y ⟩
    y ∙ ε ≡˘⟨ cong (y ∙_) (∙⁻ x) ⟩
    y ∙ (x ∙ - x) ≡˘⟨ assoc y x (- x) ⟩
    (y ∙ x) ∙ - x ≡⟨ cong (_∙ - x) p ⟩
    (z ∙ x) ∙ - x ≡⟨ assoc z x (- x) ⟩
    z ∙ (x ∙ - x) ≡⟨ cong (z ∙_) (∙⁻ x) ⟩
    z ∙ ε ≡⟨ ∙ε z ⟩
    z ∎

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

  +-monoid : Monoid ℓ
  +-monoid .Monoid.𝑆 = 𝑅
  +-monoid .Monoid._∙_ = _+_
  +-monoid .Monoid.ε = 0#
  +-monoid .Monoid.assoc = +-assoc
  +-monoid .Monoid.ε∙ = 0+
  +-monoid .Monoid.∙ε = +0

  *-monoid : Monoid ℓ
  *-monoid .Monoid.𝑆 = 𝑅
  *-monoid .Monoid._∙_ = _*_
  *-monoid .Monoid.ε = 1#
  *-monoid .Monoid.assoc = *-assoc
  *-monoid .Monoid.ε∙ = 1*
  *-monoid .Monoid.∙ε = *1

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

record LeftSemimodule {ℓ₁} (semiring : Semiring ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
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
    ⋊∅ : ∀ x → x ⋊ ∅ ≡ ∅

record SemimoduleHomomorphism[_]_⟶_
         {ℓ₁ ℓ₂ ℓ₃}
         (rng : Semiring ℓ₁)
         (from : LeftSemimodule rng ℓ₂)
         (to : LeftSemimodule rng ℓ₃) : Type (ℓ₁ ℓ⊔ ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) where

  open Semiring rng
  open LeftSemimodule from using (_⋊_; monoid)
  open LeftSemimodule to using () renaming (_⋊_ to _⋊′_; monoid to monoid′)

  field mon-homo : MonoidHomomorphism monoid ⟶ monoid′

  open MonoidHomomorphism_⟶_ mon-homo public

  field ⋊-homo : ∀ r x → f (r ⋊ x) ≡ r ⋊′ f x

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

record IsFunctor {ℓ₁ ℓ₂} (𝐹 : Type ℓ₁ → Type ℓ₂) : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
  field
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


record IsMonad {ℓ₁} {ℓ₂} (𝐹 : Type ℓ₁ → Type ℓ₂) : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
  infixl 1 _>>=_
  field
    _>>=_ : 𝐹 A → (A → 𝐹 B) → 𝐹 B
    return : A → 𝐹 A

    >>=-idˡ : (f : A → 𝐹 B) → (x : A) → (return x >>= f) ≡ f x
    >>=-idʳ : (x : 𝐹 A) → (x >>= return) ≡ x
    >>=-assoc : (xs : 𝐹 A) (f : A → 𝐹 B) (g : B → 𝐹 C) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))


record Monad ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    𝐹 : Type ℓ₁ → Type ℓ₂
    isMonad : IsMonad 𝐹
  open IsMonad isMonad public

record MonadHomomorphism_⟶_
         {ℓ₁ ℓ₂ ℓ₃}
         (from : Monad ℓ₁ ℓ₂)
         (to : Monad ℓ₁ ℓ₃) : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃) where
  module F = Monad from
  module T = Monad to

  field
    f : F.𝐹 A → T.𝐹 A
    >>=-homo : (xs : F.𝐹 A) (k : A → F.𝐹 B) → (f xs T.>>= (f ∘ k)) ≡ f (xs F.>>= k)
    return-homo : (x : A) → f (F.return x) ≡ T.return x

record IsSetMonad {ℓ₁} {ℓ₂} (𝐹 : Type ℓ₁ → Type ℓ₂) : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
  infixl 1 _>>=_
  field
    _>>=_ : 𝐹 A → (A → 𝐹 B) → 𝐹 B
    return : A → 𝐹 A

    trunc : isSet A → isSet (𝐹 A)

    >>=-idˡ   : isSet B → (f : A → 𝐹 B) → (x : A) → (return x >>= f) ≡ f x
    >>=-idʳ   : isSet A → (x : 𝐹 A) → (x >>= return) ≡ x
    >>=-assoc : isSet C → (xs : 𝐹 A) (f : A → 𝐹 B) (g : B → 𝐹 C) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

record SetMonad ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    𝐹 : Type ℓ₁ → Type ℓ₂
    isSetMonad : IsSetMonad 𝐹
  open IsSetMonad isSetMonad public

record SetMonadHomomorphism_⟶_
         {ℓ₁ ℓ₂ ℓ₃}
         (from : SetMonad ℓ₁ ℓ₂)
         (to : SetMonad ℓ₁ ℓ₃) : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃) where
  module F = SetMonad from
  module T = SetMonad to

  field
    f : F.𝐹 A → T.𝐹 A
    >>=-homo : (xs : F.𝐹 A) (k : A → F.𝐹 B) → (f xs T.>>= (f ∘ k)) ≡ f (xs F.>>= k)
    return-homo : (x : A) → f (F.return x) ≡ T.return x

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

record GradedMonad {ℓ₁} (monoid : Monoid ℓ₁) ℓ₂ ℓ₃ : Type (ℓ₁ ℓ⊔ ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) where
  open Monoid monoid
  field
    𝐹 : 𝑆 → Type ℓ₂ → Type ℓ₃
    return  : A → 𝐹 ε A
    _>>=_ : ∀ {x y} → 𝐹 x A → (A → 𝐹 y B) → 𝐹 (x ∙ y) B

  _<=<_ : ∀ {x y} → (B → 𝐹 y C) → (A → 𝐹 x B) → A → 𝐹 (x ∙ y) C
  (g <=< f) x = f x >>= g

  _>=>_ : ∀ {x y} → (A → 𝐹 x B) → (B → 𝐹 y C) → A → 𝐹 (x ∙ y) C
  (f >=> g) x = f x >>= g

  field
    >>=-idˡ : ∀ {s} (f : A → 𝐹 s B) → (x : A) → (return x >>= f) ≡[ i ≔ 𝐹 (ε∙ s i) B ]≡ (f x)
    >>=-idʳ : ∀ {s} (x : 𝐹 s A) → (x >>= return) ≡[ i ≔ 𝐹 (∙ε s i) A ]≡ x
    >>=-assoc : ∀ {x y z} (xs : 𝐹 x A) (f : A → 𝐹 y B) (g : B → 𝐹 z C) → ((xs >>= f) >>= g) ≡[ i ≔ 𝐹 (assoc x y z i) C ]≡ (xs >>= (λ x → f x >>= g))

  infixr 0 proven-bind

  proven-bind : ∀ {x y z} → 𝐹 x A → (A → 𝐹 y B) → (x ∙ y) ≡ z → 𝐹 z B
  proven-bind xs f proof = subst (flip 𝐹 _) proof (xs >>= f)

  syntax proven-bind xs f proof = xs >>=[ proof ] f

  infixr 0 proven-do
  proven-do : ∀ {x y z} → 𝐹 x A → (A → 𝐹 y B) → (x ∙ y) ≡ z → 𝐹 z B
  proven-do = proven-bind

  syntax proven-do xs (λ x → e) proof = x ← xs [ proof ] e

  map : ∀ {x} → (A → B) → 𝐹 x A → 𝐹 x B
  map f xs = xs >>=[ ∙ε _ ] (return ∘ f)

  _<*>_ : ∀ {x y} → 𝐹 x (A → B) → 𝐹 y A → 𝐹 (x ∙ y) B
  fs <*> xs = fs >>= flip map xs

  _>>=ε_ : ∀ {x} → 𝐹 x A → (A → 𝐹 ε B) → 𝐹 x B
  xs >>=ε f = xs >>=[ ∙ε _ ] f

record GradedComonad {ℓ₁} (monoid : Monoid ℓ₁) ℓ₂ : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  open Monoid monoid
  field
    𝐹 : 𝑆 → Type ℓ₂ → Type ℓ₂
    extract : 𝐹 ε A → A
    extend  : ∀ {x y} → (𝐹 y A → B) → 𝐹 (x ∙ y) A → 𝐹 x B

  _=>>_ : ∀ {x y} → 𝐹 (x ∙ y) A → (𝐹 y A → B) → 𝐹 x B
  _=>>_ = flip extend

  proven-cobind : ∀ {x y z} → (𝐹 y A → B) → x ∙ y ≡ z → 𝐹 z A → 𝐹 x B
  proven-cobind k prf = subst (λ zs → 𝐹 zs _ → _) prf (extend k)

  syntax proven-cobind f prf xs = xs =>>[ prf ] f

  _=<=_ : ∀ {x y} → (𝐹 x B → C) → (𝐹 y A → B) → 𝐹 (x ∙ y) A → C
  (g =<= f) x = g (extend f x)

  _=>=_ : ∀ {x y} → (𝐹 y A → B) → (𝐹 x B → C) → 𝐹 (x ∙ y) A → C
  _=>=_ = flip _=<=_


  field
    =>>-idˡ : ∀ {x} {B : Type ℓ₂} → (f : 𝐹 x A → B) → PathP (λ i → 𝐹 (ε∙ x i) A → B) (extract =<= f) f
    =>>-idʳ : ∀ {x} {B : Type ℓ₂} → (f : 𝐹 x A → B) → PathP (λ i → 𝐹 (∙ε x i) A → B) (f =<= extract) f
    =>>-assoc : ∀ {x y z} {D : Type ℓ₂} → (f : 𝐹 x C → D) (g : 𝐹 y B → C) (h : 𝐹 z A → B) →
          PathP (λ i → 𝐹 (assoc x y z i) A → D) ((f =<= g) =<= h) (f =<= (g =<= h))

  {-# INLINE proven-cobind #-}

  infixr 1 codo-syntax
  codo-syntax : ∀ {x y} → 𝐹 (x ∙ y) A → (𝐹 y A → B) → 𝐹 x B
  codo-syntax = _=>>_

  syntax codo-syntax xs (λ x → r) = x ↢ xs ; r

  infixr 1 proven-codo-syntax
  proven-codo-syntax : ∀ {x y z} → 𝐹 z A → (𝐹 y A → B) → x ∙ y ≡ z → 𝐹 x B
  proven-codo-syntax xs k p = proven-cobind k p xs

  syntax proven-codo-syntax xs (λ x → r) prf = x ↢ xs [ prf ]; r

  map : ∀ {x} → (A → B) → 𝐹 x A → 𝐹 x B
  map f = proven-cobind (f ∘′ extract) (∙ε _)
  {-# INLINE map #-}

  -- open import Cubical.Foundations.Prelude using (fromPathP)

  -- map-id : ∀ {x} → (xs : 𝐹 x A) → map id xs ≡ xs
  -- map-id xs = cong (_$ xs) (fromPathP (=>>-idʳ id))

  -- map-comp : ∀ {x} (g : B → C) (f : A → B) → map {x = x} g ∘ map f ≡ map {x = x} (g ∘ f)
  -- map-comp g f = let p = =>>-assoc extract (g ∘′ extract) (f ∘′ extract) in {!!}

record SGradedComonad {ℓ₁} (semiring : Semiring ℓ₁) ℓ₂ ℓ₃ : Type (ℓ₁ ℓ⊔ ℓsuc (ℓ₂ ℓ⊔ ℓ₃)) where
  open Semiring semiring
  field
    gradedComonad : GradedComonad +-monoid ℓ₂
  open GradedComonad gradedComonad
  field
    pure  : ∀ {x} → 𝐹 x A
    _<*>_ : ∀ {x} → 𝐹 x (A → B) → 𝐹 x A → 𝐹 x B
    separate : ∀ {x y} → 𝐹 (x + y) A → 𝐹 x A × 𝐹 y A

record MatchedPair {ℓ₁ ℓ₂} (R : Monoid ℓ₁) (E : Monoid ℓ₂) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  open Monoid R using ()    renaming (𝑆 to 𝑅; _∙_ to _*_; ε to r1)
  open Monoid E using (_∙_) renaming (𝑆 to 𝐸; ε to e1)

  field
    ι : 𝑅 → 𝐸 → 𝑅
    κ : 𝑅 → 𝐸 → 𝐸

    law1 : ∀ x → ι x e1 ≡ x
    law2 : ∀ x → ι r1 x ≡ r1
    law3 : ∀ x → κ r1 x ≡ x
    law4 : ∀ x → κ x e1 ≡ e1

    law5 : ∀ x y z → ι x (y ∙ z) ≡ ι (ι x y) z
    law6 : ∀ x y z → ι (x * y) z ≡ ι x (κ y z) * ι y z
    law7 : ∀ x y z → κ (x * y) z ≡ κ x (κ y z)
    law8 : ∀ x y z → κ x (y ∙ z) ≡ κ x y ∙ κ (ι x y) z

  
