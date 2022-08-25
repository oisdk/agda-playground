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

module _ {ℓ} (𝑆 : Type ℓ) where
  record  Semigroup : Type ℓ where
    infixl 6 _∙_
    field
      _∙_    : 𝑆 → 𝑆 → 𝑆
      assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  record  Monoid : Type ℓ where
    infixl 6 _∙_
    field
      _∙_    : 𝑆 → 𝑆 → 𝑆
      ε      : 𝑆
      assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      ε∙     : ∀ x → ε ∙ x ≡ x
      ∙ε     : ∀ x → x ∙ ε ≡ x

    semigroup : Semigroup
    semigroup = record
      { _∙_ = _∙_; assoc = assoc }


  record Group : Type ℓ where
    field
      monoid : Monoid
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

  record CommutativeMonoid : Type ℓ where
    field
      monoid : Monoid
    open Monoid monoid public
    field
      comm : Commutative _∙_

  record Semilattice : Type ℓ where
    field
      commutativeMonoid : CommutativeMonoid
    open CommutativeMonoid commutativeMonoid public
    field
      idem : Idempotent _∙_

  record NearSemiring : Type ℓ where
    infixl 6 _+_
    infixl 7 _*_
    field
      _+_ : 𝑆 → 𝑆 → 𝑆
      _*_ : 𝑆 → 𝑆 → 𝑆
      1# : 𝑆
      0# : 𝑆
      +-assoc : Associative _+_
      *-assoc : Associative _*_
      0+ : Identityˡ _+_ 0#
      +0 : Identityʳ _+_ 0#
      1* : Identityˡ _*_ 1#
      *1 : Identityʳ _*_ 1#
      0* : Zeroˡ _*_ 0#
      ⟨+⟩* : _*_ Distributesˡ _+_

    +-monoid : Monoid
    +-monoid .Monoid._∙_ = _+_
    +-monoid .Monoid.ε = 0#
    +-monoid .Monoid.assoc = +-assoc
    +-monoid .Monoid.ε∙ = 0+
    +-monoid .Monoid.∙ε = +0

    *-monoid : Monoid
    *-monoid .Monoid._∙_ = _*_
    *-monoid .Monoid.ε = 1#
    *-monoid .Monoid.assoc = *-assoc
    *-monoid .Monoid.ε∙ = 1*
    *-monoid .Monoid.∙ε = *1

  record Semiring : Type ℓ where
    field
      nearSemiring : NearSemiring
    open NearSemiring nearSemiring public
    field
      +-comm : Commutative _+_
      *0 : Zeroʳ _*_ 0#
      *⟨+⟩ : _*_ Distributesʳ _+_

  record IdempotentSemiring : Type ℓ where
    field
      semiring : Semiring
    open Semiring semiring public
    field
      +-idem : Idempotent _+_

  record CommutativeSemiring : Type ℓ where
    field
      semiring : Semiring
    open Semiring semiring public
    field
      *-comm : Commutative _*_

  record StarSemiring : Type ℓ where
    field semiring : Semiring
    open Semiring semiring public
    field
      _⋆ : 𝑆 → 𝑆
      star-iterʳ : ∀ x → x ⋆ ≡ 1# + x * x ⋆
      star-iterˡ : ∀ x → x ⋆ ≡ 1# + x ⋆ * x
    _⁺ : 𝑆 → 𝑆
    x ⁺ = x * x ⋆

record LeftSemimodule {ℓ₁ ℓ₂} {𝑆 : Type ℓ₁} (semiring : Semiring 𝑆) (𝑉 : Type ℓ₂) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  open Semiring semiring public
  field semimodule : CommutativeMonoid 𝑉
  open CommutativeMonoid semimodule renaming (_∙_ to _∪_) public
    renaming ( assoc to ∪-assoc
             ; ε∙ to ∅∪
             ; ∙ε to ∪∅
             ; ε to ∅
             )
  infixr 7 _⋊_
  field
    _⋊_ : 𝑆 → 𝑉 → 𝑉
    ⟨*⟩⋊ : ∀ x y z → (x * y) ⋊ z ≡ x ⋊ (y ⋊ z)
    ⟨+⟩⋊ : ∀ x y z → (x + y) ⋊ z ≡ (x ⋊ z) ∪ (y ⋊ z)
    ⋊⟨∪⟩ : _⋊_ Distributesʳ _∪_
    1⋊ : Identityˡ _⋊_ 1#
    0⋊ : ∀ x → 0# ⋊ x ≡ ∅
    ⋊∅ : ∀ x → x ⋊ ∅ ≡ ∅

record MonoidHomomorphism_⟶_
        {ℓ₁ ℓ₂} {𝑆 : Type ℓ₁} {𝑇 : Type ℓ₂}
        (from : Monoid 𝑆)
        (to   : Monoid 𝑇)
      : Type (ℓ₁ ℓ⊔ ℓ₂) where
  open Monoid from
  open Monoid to
    renaming ( _∙_ to _⊙_
             ; ε to ⓔ)
  field
    f : 𝑆 → 𝑇
    ∙-homo : ∀ x y → f (x ∙ y) ≡ f x ⊙ f y
    ε-homo : f ε ≡ ⓔ

record SemimoduleHomomorphism[_]_⟶_
        {ℓ₁ ℓ₂ ℓ₃} {𝑆 : Type ℓ₁} {𝑉₁ : Type ℓ₂} {𝑉₂ : Type ℓ₃}
        (rng : Semiring 𝑆)
        (from : LeftSemimodule rng 𝑉₁)
        (to : LeftSemimodule rng 𝑉₂) : Type (ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃) where

  open Semiring rng
  open LeftSemimodule from using (_⋊_; monoid)
  open LeftSemimodule to using () renaming (_⋊_ to _⋊′_; monoid to monoid′)

  field mon-homo : MonoidHomomorphism monoid ⟶ monoid′

  open MonoidHomomorphism_⟶_ mon-homo public

  field ⋊-homo : ∀ r x → f (r ⋊ x) ≡ r ⋊′ f x


module _ {ℓ₁ ℓ₂} (𝐹 : Type ℓ₁ → Type ℓ₂) where

  record Functor : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    field
      map : (A → B) → 𝐹 A → 𝐹 B
      map-id : map (id {ℓ₁} {A}) ≡ id
      map-comp : (f : B → C) → (g : A → B) → map (f ∘ g) ≡ map f ∘ map g

  record Applicative : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    infixl 5 _<*>_
    field
      pure : A → 𝐹 A
      _<*>_ : 𝐹 (A → B) → 𝐹 A → 𝐹 B

    map : (A → B) → 𝐹 A → 𝐹 B
    map f = _<*>_ (pure f)
    field
      pure-homo : (f : A → B) → (x : A) → pure f <*> (pure x) ≡ pure (f x)
      <*>-interchange : (u : 𝐹 (A → B)) → (y : A) → u <*> pure y ≡ map (_$ y) u
      <*>-comp : (u : 𝐹 (B → C)) → (v : 𝐹 (A → B)) → (w : 𝐹 A) → pure _∘′_ <*> u <*> v <*> w ≡ u <*> (v <*> w)


  record Monad : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    infixl 1 _>>=_
    field
      _>>=_ : 𝐹 A → (A → 𝐹 B) → 𝐹 B
      return : A → 𝐹 A

      >>=-idˡ : (f : A → 𝐹 B) → (x : A) → (return x >>= f) ≡ f x
      >>=-idʳ : (x : 𝐹 A) → (x >>= return) ≡ x
      >>=-assoc : (xs : 𝐹 A) (f : A → 𝐹 B) (g : B → 𝐹 C) → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))

    mmap : (A → B) → 𝐹 A → 𝐹 B
    mmap f xs = xs >>= (return ∘ f)

  record Comonad : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    field
      extend : (𝐹 A → B) → 𝐹 A → 𝐹 B
      extract : 𝐹 A → A

    infixl 1 _=>>_
    _=>>_ : 𝐹 A → (𝐹 A → B) → 𝐹 B
    _=>>_ = flip extend

    cmap : (A → B) → 𝐹 A → 𝐹 B
    cmap f xs = xs =>> (f ∘ extract)

    -- liftA2 : (A → B → C) → 𝐹 A → 𝐹 B → 𝐹 C
    -- liftA2 f xs ys = xs =>> λ x → {!ys =>> λ y → {!!}!}


  record Alternative : Type (ℓsuc ℓ₁ ℓ⊔ ℓ₂) where
    field
      applicative : Applicative
    open Applicative applicative public
    field
      0# : 𝐹 A
      _<|>_ : 𝐹 A → 𝐹 A → 𝐹 A
      <|>-idˡ : (x : 𝐹 A) → 0# <|> x ≡ x
      <|>-idʳ : (x : 𝐹 A) → x <|> 0# ≡ x
      0-annˡ : (x : 𝐹 A) → 0# <*> x ≡ 0# {B}
      <|>-distrib : (x y : 𝐹 (A → B)) → (z : 𝐹 A) → (x <|> y) <*> z ≡ (x <*> z) <|> (y <*> z)

--   record MonadPlus ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
--     field
--       monad : Monad ℓ₁ ℓ₂
--     open Monad monad public
--     field
--       0# : 𝐹 A
--       _<|>_ : 𝐹 A → 𝐹 A → 𝐹 A
--       <|>-idˡ : (x : 𝐹 A) → 0# <|> x ≡ x
--       <|>-idʳ : (x : 𝐹 A) → x <|> 0# ≡ x
--       0-annˡ : (x : A → 𝐹 B) → (0# >>= x) ≡ 0#
--       <|>-distrib : (x y : 𝐹 A) → (z : A → 𝐹 B) → ((x <|> y) >>= z) ≡ (x >>= z) <|> (y >>= z)

--   Endo : Type a → Type a
--   Endo A = A → A

--   endoMonoid : ∀ {a} → Type a → Monoid a
--   endoMonoid A .Monoid.𝑆 = Endo A
--   endoMonoid A .Monoid.ε x = x
--   endoMonoid A .Monoid._∙_ f g x = f (g x)
--   endoMonoid A .Monoid.assoc _ _ _ = refl
--   endoMonoid A .Monoid.ε∙ _ = refl
--   endoMonoid A .Monoid.∙ε _ = refl

--   record Foldable ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
--     field
--       𝐹 : Type ℓ₁ → Type ℓ₂
--     open Monoid ⦃ ... ⦄
--     field
--       foldMap : {A : Type ℓ₁} ⦃ _ : Monoid ℓ₁ ⦄ → (A → 𝑆) → 𝐹 A → 𝑆
--     foldr : {A B : Type ℓ₁} → (A → B → B) → B → 𝐹 A → B
--     foldr f b xs = foldMap ⦃ endoMonoid _ ⦄ f xs b
--     
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

module _ {ℓ₁} {𝑆 : Type ℓ₁} (monoid : Monoid 𝑆) {ℓ₂} (𝐹 : 𝑆 → Type ℓ₂ → Type ℓ₂) where
  open Monoid monoid
  record GradedMonad : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
    field
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

  record GradedComonad : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
    field
      extract : 𝐹 ε A → A
      extend  : ∀ {x y} → (𝐹 y A → B) → 𝐹 (x ∙ y) A → 𝐹 x B

    extend[_] : ∀ {x y z} → x ∙ y ≡ z → (𝐹 y A → B) → 𝐹 z A → 𝐹 x B
    extend[ p ] k = subst (λ w → (𝐹 w _ → _)) p (extend k)

    _=>>_ : ∀ {x y} → 𝐹 (x ∙ y) A → (𝐹 y A → B) → 𝐹 x B
    _=>>_ = flip extend

    proven-cobind : ∀ {x y z} → (𝐹 y A → B) → x ∙ y ≡ z → 𝐹 z A → 𝐹 x B
    proven-cobind k prf = extend[ prf ] k

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
    {-# INLINE extend[_] #-}

    infixr 1 codo-syntax
    codo-syntax : ∀ {x y} → 𝐹 (x ∙ y) A → (𝐹 y A → B) → 𝐹 x B
    codo-syntax = _=>>_

    syntax codo-syntax xs (λ x → r) = x ↢ xs ; r

    infixr 1 proven-codo-syntax
    proven-codo-syntax : ∀ {x y z} → 𝐹 z A → (𝐹 y A → B) → x ∙ y ≡ z → 𝐹 x B
    proven-codo-syntax xs k p = proven-cobind k p xs

    syntax proven-codo-syntax xs (λ x → r) prf = x ↢ xs [ prf ]; r

    map : ∀ {x} → (A → B) → 𝐹 x A → 𝐹 x B
    map f = extend[ ∙ε _ ] (f ∘′ extract)
    {-# INLINE map #-}

    open import Cubical.Foundations.Prelude using (fromPathP; transportRefl; substRefl)

    map-id : ∀ {x} → (xs : 𝐹 x A) → map id xs ≡ xs
    map-id xs = cong (_$ xs) (fromPathP (=>>-idʳ id))

    extract-extend : ∀ {x} (xs : 𝐹 x A) → extract (extend[ ε∙ x ] id xs) ≡ xs
    extract-extend {A = A} {x = x} xs =
      cong extract (J (λ y p → (xs : 𝐹 y A) → extend[ p ] id xs ≡ extend id (subst (flip 𝐹 A) (sym p) xs)) (λ xs → cong (_$ xs) (transportRefl (extend id))  ; cong (extend id) (sym (transportRefl xs))) (ε∙ x) xs ) ;
      sym (transportRefl _) ;
      cong (_$ xs) (fromPathP (=>>-idˡ {x = x} id))

    open import Path.Reasoning

    -- map-comp : ∀ {x} (g : B → C) (f : A → B) → map {x = x} g ∘ map f ≡ map {x = x} (g ∘ f)
    -- map-comp {x = x} g f = funExt λ xs →
    --   map g (map f xs) ≡⟨⟩
    --   extend[ ∙ε x ] (g ∘ extract) (extend[ ∙ε x ] (f ∘ extract) xs) ≡⟨ {!!} ⟩
    --   extend[ ∙ε x ] (g ∘ f ∘ extract) xs ≡⟨⟩
    --   map (g ∘ f) xs ∎

record SGradedComonad {ℓ₁ ℓ₂} {𝑆 : Type ℓ₁} (semiring : Semiring 𝑆) (𝐹 : 𝑆 → Type ℓ₂ → Type ℓ₂) : Type (ℓ₁ ℓ⊔ ℓsuc ℓ₂) where
  open Semiring semiring
  field gradedComonad : GradedComonad *-monoid 𝐹
  open GradedComonad gradedComonad
  field
    pure  : ∀ {x} → 𝐹 x A
    _<*>_ : ∀ {x} → 𝐹 x (A → B) → 𝐹 x A → 𝐹 x B
    separate : ∀ {x y} → 𝐹 (x + y) A → 𝐹 x A × 𝐹 y A

record MatchedPair {ℓ₁ ℓ₂} {𝑆 : Type ℓ₁} {𝐸 : Type ℓ₂} (R : Monoid 𝑆) (E : Monoid 𝐸) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  open Monoid R using ()    renaming (_∙_ to _*_; ε to r1)
  open Monoid E using (_∙_) renaming (ε to e1)

  field
    ι : 𝑆 → 𝐸 → 𝑆
    κ : 𝑆 → 𝐸 → 𝐸

    law1 : ∀ x → ι x e1 ≡ x
    law2 : ∀ x → ι r1 x ≡ r1
    law3 : ∀ x → κ r1 x ≡ x
    law4 : ∀ x → κ x e1 ≡ e1

    law5 : ∀ x y z → ι x (y ∙ z) ≡ ι (ι x y) z
    law6 : ∀ x y z → ι (x * y) z ≡ ι x (κ y z) * ι y z
    law7 : ∀ x y z → κ (x * y) z ≡ κ x (κ y z)
    law8 : ∀ x y z → κ x (y ∙ z) ≡ κ x y ∙ κ (ι x y) z


