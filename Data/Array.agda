{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Array where

open import Data.Binary
open import Prelude

private
  variable
    ns : 𝔹

record 2× {a} (A : Type a) : Type a where
  constructor _⊛_
  field
    pr₁ pr₂ : A
open 2× public

infixr 5 _∷₁_ _∷₂_ _∷_
data Array {a} (A : Type a) : 𝔹 → Type a where
  [] : Array A 0ᵇ
  _∷₁_ :    A → Array (2× A) ns → Array A (1ᵇ ns)
  _∷₂_ : 2× A → Array (2× A) ns → Array A (2ᵇ ns)

_∷_ : A → Array A ns → Array A (inc ns)
x  ∷ [] = x ∷₁ []
x₁ ∷ x₂ ∷₁ xs = (x₁ ⊛ x₂) ∷₂ xs
x₁ ∷ x₂ ∷₂ xs = x₁ ∷₁ x₂ ∷ xs

open import Data.Binary.Order

mutual
  index : ∀ is {js} → Array A js → is < js → A
  index 0ᵇ      (x ∷₁ xs) p = x
  index 0ᵇ      (x ∷₂ xs) p = pr₁ x
  index (1ᵇ is) xs        p = index₂1ᵇ is xs p
  index (2ᵇ is) (x ∷₁ xs) p = pr₂ (index is xs p)
  index (2ᵇ is) (x ∷₂ xs) p = pr₁ (index is xs p)

  index₂1ᵇ : ∀ is {js} → Array A js → 1ᵇ is < js → A
  index₂1ᵇ is      (x ∷₁ xs) p = pr₁ (index is xs p)
  index₂1ᵇ 0ᵇ      (x ∷₂ xs) p = pr₂ x
  index₂1ᵇ (1ᵇ is) (x ∷₂ xs) p = pr₂ (index₃ is xs p)
  index₂1ᵇ (2ᵇ is) (x ∷₂ xs) p = pr₂ (index₂2ᵇ is xs p)

  index₂2ᵇ : ∀ is {js} → Array A js → 2ᵇ is ≤ js → A
  index₂2ᵇ is      (x ∷₁ xs) p = pr₁ (index is xs p)
  index₂2ᵇ 0ᵇ      (x ∷₂ xs) p = pr₂ x
  index₂2ᵇ (1ᵇ is) (x ∷₂ xs) p = pr₂ (index₃ is xs p)
  index₂2ᵇ (2ᵇ is) (x ∷₂ xs) p = pr₂ (index₂2ᵇ is xs p)

  index₃ : ∀ is {js} → Array A js → 1ᵇ is ≤ js → A
  index₃ 0ᵇ      (x ∷₁ xs) p = x
  index₃ 0ᵇ      (x ∷₂ xs) p = pr₁ x
  index₃ (1ᵇ is) (x ∷₁ xs) p = pr₂ (index₃ is xs p)
  index₃ (1ᵇ is) (x ∷₂ xs) p = pr₁ (index₃ is xs p)
  index₃ (2ᵇ is) (x ∷₁ xs) p = pr₂ (index₂2ᵇ is xs p)
  index₃ (2ᵇ is) (x ∷₂ xs) p = pr₁ (index₂2ᵇ is xs p)

index? : 𝔹 → Array A ns → Maybe A
index? {ns = ns} is xs with T? (is <ᴮ ns)
... | no  _ = nothing
... | yes p = just (index is xs p)

_!_ : ∀ {js} → Array A js → ∀ is → { p : is < js } → A
_!_ xs is {p} = index is xs p

open import Lens

head1ᵇ : Lens (Array A (1ᵇ ns)) A
head1ᵇ .into (x ∷₁ xs) = lens-part x (_∷₁ xs)
head1ᵇ .get-set (x ∷₁ xs) v i = v
head1ᵇ .set-get (x ∷₁ xs) i = x ∷₁ xs
head1ᵇ .set-set (x ∷₁ xs) v₁ v₂ i = v₂ ∷₁ xs

head2ᵇ : Lens (Array A (2ᵇ ns)) (2× A)
head2ᵇ .into (x ∷₂ xs) = lens-part x (_∷₂ xs)
head2ᵇ .get-set (x ∷₂ xs) v i = v
head2ᵇ .set-get (x ∷₂ xs) i = x ∷₂ xs
head2ᵇ .set-set (x ∷₂ xs) v₁ v₂ i = v₂ ∷₂ xs
{-# INLINE head2ᵇ #-}

tail1ᵇ : Lens (Array A (1ᵇ ns)) (Array (2× A) ns)
tail1ᵇ .into (x ∷₁ xs) = lens-part xs (x ∷₁_)
tail1ᵇ .get-set (x ∷₁ xs) v i = v
tail1ᵇ .set-get (x ∷₁ xs) i = x ∷₁ xs
tail1ᵇ .set-set (x ∷₁ xs) v₁ v₂ i = x ∷₁ v₂

tail2ᵇ : Lens (Array A (2ᵇ ns)) (Array (2× A) ns)
tail2ᵇ .into (x ∷₂ xs) = lens-part xs (x ∷₂_)
tail2ᵇ .get-set (x ∷₂ xs) v i = v
tail2ᵇ .set-get (x ∷₂ xs) i = x ∷₂ xs
tail2ᵇ .set-set (x ∷₂ xs) v₁ v₂ i = x ∷₂ v₂

⦅pr₁⦆ : Lens (2× A) A
⦅pr₁⦆ .into (x ⊛ y) = lens-part x (_⊛ y)
⦅pr₁⦆ .get-set s v i = v
⦅pr₁⦆ .set-get s i = s
⦅pr₁⦆ .set-set s v₁ v₂ i = v₂ ⊛ s .pr₂

⦅pr₂⦆ : Lens (2× A) A
⦅pr₂⦆ .into (x ⊛ y) = lens-part y (x ⊛_)
⦅pr₂⦆ .get-set s v i = v
⦅pr₂⦆ .set-get s i = s
⦅pr₂⦆ .set-set s v₁ v₂ i = s .pr₁ ⊛ v₂

mutual
  ind : ∀ is {js} → is < js → Lens (Array A js) A
  ind 0ᵇ      {1ᵇ js} p = head1ᵇ
  ind 0ᵇ      {2ᵇ js} p = head2ᵇ ⋯ ⦅pr₁⦆
  ind (1ᵇ is) {js}    p = ind₂1ᵇ is p
  ind (2ᵇ is) {1ᵇ js} p = tail1ᵇ ⋯ ind is p ⋯ ⦅pr₂⦆
  ind (2ᵇ is) {2ᵇ js} p = tail2ᵇ ⋯ ind is p ⋯ ⦅pr₁⦆

  ind₂1ᵇ : ∀ is {js} → 1ᵇ is < js → Lens (Array A js) A
  ind₂1ᵇ is      {1ᵇ js} p = tail1ᵇ ⋯ ind is p ⋯ ⦅pr₁⦆
  ind₂1ᵇ 0ᵇ      {2ᵇ js} p = head2ᵇ ⋯ ⦅pr₂⦆
  ind₂1ᵇ (1ᵇ is) {2ᵇ js} p = tail2ᵇ ⋯ ind₃ is p ⋯ ⦅pr₂⦆
  ind₂1ᵇ (2ᵇ is) {2ᵇ js} p = tail2ᵇ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₂⦆

  ind₂2ᵇ : ∀ is {js} → 2ᵇ is ≤ js → Lens (Array A js) A
  ind₂2ᵇ is      {1ᵇ js} p = tail1ᵇ ⋯ ind is p ⋯ ⦅pr₁⦆
  ind₂2ᵇ 0ᵇ      {2ᵇ js} p = head2ᵇ ⋯ ⦅pr₂⦆
  ind₂2ᵇ (1ᵇ is) {2ᵇ js} p = tail2ᵇ ⋯ ind₃ is p ⋯ ⦅pr₂⦆
  ind₂2ᵇ (2ᵇ is) {2ᵇ js} p = tail2ᵇ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₂⦆

  ind₃ : ∀ is {js} → 1ᵇ is ≤ js → Lens (Array A js) A
  ind₃ 0ᵇ      {1ᵇ js} p = head1ᵇ
  ind₃ 0ᵇ      {2ᵇ js} p = head2ᵇ ⋯ ⦅pr₁⦆
  ind₃ (1ᵇ is) {1ᵇ js} p = tail1ᵇ ⋯ ind₃ is p ⋯ ⦅pr₂⦆
  ind₃ (1ᵇ is) {2ᵇ js} p = tail2ᵇ ⋯ ind₃ is p ⋯ ⦅pr₁⦆
  ind₃ (2ᵇ is) {1ᵇ js} p = tail1ᵇ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₂⦆
  ind₃ (2ᵇ is) {2ᵇ js} p = tail2ᵇ ⋯ ind₂2ᵇ is p ⋯ ⦅pr₁⦆

at : ∀ is {js} → {p : is < js} → Lens (Array A js) A
at is {p = p} = ind is p


-- open import Data.Binary.Literals
-- open import Data.Nat.Literals
-- open import Literals.Number

-- e : Array ℕ 100 →  ℕ → Array ℕ 100
-- e xs n = xs [ at 10 ]≔ n


-- e : Array ℕ _
-- e = (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) [ at 3 ]≔ 10


foldr : (A → B → B) → B → Array A ns → B
foldr f b [] = b
foldr f b (x ∷₁ xs) = f x (foldr (λ { (x₁ ⊛ x₂) b → f x₁ (f x₂ b) }) b xs)
foldr f b ((x₁ ⊛ x₂) ∷₂ xs) = f x₁ (f x₂ (foldr (λ { (x₁ ⊛ x₂) b → f x₁ (f x₂ b)}) b xs))

import Data.Nat as ℕ

foldrP : ∀ {p} (P : ℕ → Type p) → (∀ {n} → A → P n → P (suc n)) → P zero → Array A ns → P ⟦ ns ⇓⟧
foldrP P f b [] = b
foldrP P f b (x ∷₁ xs) = f x (foldrP (λ n → P (n ℕ.* 2)) (λ { (x₁ ⊛ x₂) b → f x₁ (f x₂ b) }) b xs)
foldrP P f b ((x₁ ⊛ x₂) ∷₂ xs) = f x₁ (f x₂ (foldrP (λ n → P (n ℕ.* 2)) (λ { (x₁ ⊛ x₂) b → f x₁ (f x₂ b)}) b xs))

-- -- upTo : ∀ n → Array ℕ ⟦ n ⇑⟧
-- -- upTo n = go n zero
-- --   where
-- --   go : ∀ n m → Array ℕ ⟦ n ⇑⟧
-- --   go zero    m = []
-- --   go (suc n) m = m ∷ go n (suc m)

-- -- import Data.List as List
-- -- import Data.Nat.Properties as ℕ

-- -- index-test : ℕ → Type₀
-- -- index-test n = List.map (λ i → index? ⟦ i ⇑⟧ arr) nums ≡ List.map just nums
-- --   where
-- --   arr : Array ℕ ⟦ n ⇑⟧
-- --   arr = upTo n

-- --   nums : List.List ℕ
-- --   nums = 0 List.⋯ ℕ.pred n

-- -- _ : index-test 33
-- -- _ = refl
