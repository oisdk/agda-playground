module Data.Dyck.Sized where

open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head; foldl′)

open import Cubical.Foundations.Prelude using (substRefl)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Data.Nat.Properties using (isSetℕ)

private variable
    n m k : ℕ
    n⊙ m⊙ k⊙ : ℕ → ℕ

--------------------------------------------------------------------------------
-- Tree
--------------------------------------------------------------------------------

data Tree : Type where
  ⟨⟩ : Tree
  _*_ : Tree → Tree → Tree

size⊙ : Tree → ℕ → ℕ
size⊙ ⟨⟩ = suc
size⊙ (xs * ys) = size⊙ xs ∘ size⊙ ys

size : Tree → ℕ
size t = size⊙ t zero

--------------------------------------------------------------------------------
-- Dyck Word
--------------------------------------------------------------------------------

infixr 6 ⟨_ ⟩_
data Dyck : ℕ → ℕ → Type where
  ⟩! : Dyck 1 0
  ⟨_ : Dyck (1 + n) m → Dyck n (1 + m)
  ⟩_ : Dyck (1 + n) m → Dyck (2 + n) m

--------------------------------------------------------------------------------
-- Tree to Stack
--------------------------------------------------------------------------------

tree→stack⊙ : (t : Tree) → Dyck (suc m) k → Dyck m (size⊙ t k)
tree→stack⊙ ⟨⟩         = ⟨_
tree→stack⊙ (xs * ys) = tree→stack⊙ xs ∘ tree→stack⊙ ys ∘ ⟩_

tree→stack : (t : Tree) → Dyck 0 (size t)
tree→stack tr = tree→stack⊙ tr ⟩!

--------------------------------------------------------------------------------
-- Stack to Tree
--------------------------------------------------------------------------------

stack→tree⊙ : Dyck n m → Vec Tree n → Tree
stack→tree⊙ ⟩!     (v ∷ [])       = v
stack→tree⊙ (⟨ is) st             = stack→tree⊙ is (⟨⟩ ∷ st)
stack→tree⊙ (⟩ is) (t₁ ∷ t₂ ∷ st) = stack→tree⊙ is (t₂ * t₁ ∷ st)

stack→tree : Dyck 0 n → Tree
stack→tree ds = stack→tree⊙ ds []

--------------------------------------------------------------------------------
-- Size lemma
--------------------------------------------------------------------------------

stack→tree-size⊙ :  {st : Vec Tree n} (is : Dyck n m) →
 size (stack→tree⊙ is st) ≡ foldl′ size⊙ m st
stack→tree-size⊙ ⟩!     = refl
stack→tree-size⊙ (⟨ is) = stack→tree-size⊙ is
stack→tree-size⊙ (⟩ is) = stack→tree-size⊙ is

--------------------------------------------------------------------------------
-- Roundtrip
--------------------------------------------------------------------------------

tree→stack→tree⊙ :  {is : Dyck (1 + n) m} {st : Vec Tree n} (e : Tree) →
  stack→tree⊙ (tree→stack⊙ e is) st ≡ stack→tree⊙ is (e ∷ st)
tree→stack→tree⊙ ⟨⟩         = refl
tree→stack→tree⊙ (xs * ys) = tree→stack→tree⊙ xs ; tree→stack→tree⊙ ys

foldlNN : ∀ {A : Type a} {p} (P : ℕ → ℕ → Type p) →
          (f : A → ℕ → ℕ) →
          (∀ {n m} → (x : A) → P (suc n) m → P n (f x m)) →
          P n m →
          (xs : Vec A n) → P zero (foldl′ f m xs)
foldlNN {n = zero} P f s b xs = b
foldlNN {n = suc n} P f s b (x ∷ xs) = foldlNN P f s (s x b) xs


stack→tree→stack⊙ :  {st : Vec Tree n} (is : Dyck n m) →
 subst (Dyck 0) (stack→tree-size⊙ is) (tree→stack (stack→tree⊙ is st))
   ≡ foldlNN Dyck size⊙ tree→stack⊙ is st
stack→tree→stack⊙  ⟩!       = substRefl {B = Dyck 0} _
stack→tree→stack⊙ (⟨ is) = stack→tree→stack⊙ is
stack→tree→stack⊙ (⟩ is) = stack→tree→stack⊙ is

--------------------------------------------------------------------------------
-- Isomorphism
--------------------------------------------------------------------------------

STree : ℕ → Type
STree = fiber size

tree-stack : STree n ⇔ Dyck 0 n
tree-stack .fun (t , n) = subst (Dyck 0) n (tree→stack t)
tree-stack .inv st .fst = stack→tree st
tree-stack .inv st .snd = stack→tree-size⊙ st
tree-stack .leftInv  (t , sz≡) =
  Σ≡Prop
  (λ _ → isSetℕ _ _)
  (J
    (λ n sz≡ → stack→tree (subst (Dyck 0) sz≡ (tree→stack t)) ≡ t)
    (cong stack→tree (substRefl {B = Dyck 0} (tree→stack t)) ; tree→stack→tree⊙ t) sz≡)
tree-stack .rightInv st = stack→tree→stack⊙ st

--------------------------------------------------------------------------------
-- Finite
--------------------------------------------------------------------------------

open import Data.List

support-dyck : ∀ n m → List (Dyck n m)
support-dyck = λ n m → sup-k n m id []
  module ListDyck where
  Diff : Type → Type₁
  Diff A = ∀ {B : Type} → (A → B) → List B → List B

  infixr 5 _++′_
  _++′_ : Diff A → Diff A → Diff A
  xs ++′ ys = λ k → xs k ∘ ys k

  mutual
    sup-k : ∀ n m → Diff (Dyck n m)
    sup-k n m = end n m ++′ lefts n m  ++′ rights n m

    lefts : ∀ n m → Diff (Dyck n m)
    lefts n zero    k = id
    lefts n (suc m) k = sup-k (suc n) m (k ∘ ⟨_)

    rights : ∀ n m → Diff (Dyck n m)
    rights (suc (suc n)) m k = sup-k (suc n) m (k ∘ ⟩_)
    rights _             m k = id

    end : ∀ n m → Diff (Dyck n m)
    end 1 0 k xs = k ⟩! ∷ xs
    end _ _ k = id

open import Data.List.Membership
open import Data.Fin

cover-dyck : (x : Dyck n m) → x ∈ support-dyck n m
cover-dyck x = go _ _ x id []
  where
  open ListDyck

  mutual
    pushLefts : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ lefts n m k xs
    pushLefts n (suc m) k = pushSup (suc n) m (λ z → k (⟨ z))
    pushLefts _ zero    k x xs p = p

    pushEnd : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ end n m k xs
    pushEnd 0 m k x xs p = p
    pushEnd 1 0 k x xs (i , p) = fs i , p
    pushEnd 1 (suc m) k x xs p = p
    pushEnd (suc (suc n)) m k x xs p = p

    pushRights : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ rights n m k xs
    pushRights (suc (suc n)) m k = pushSup (suc n) m λ z → k (⟩ z)
    pushRights 1 _ _ _ _ p = p
    pushRights 0 _ _ _ _ p = p

    pushSup : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ sup-k n m k xs
    pushSup n m k x xs p = pushEnd n m k x (lefts n m k (rights n m k xs)) (pushLefts n m k x (rights n m k xs) (pushRights n m k x xs p))

  go : ∀ n m → (x : Dyck n m) → (k : Dyck n m → A) → (xs : List A) → k x ∈ sup-k n m k xs
  go .1 .0 ⟩! k xs = f0 , refl
  go 0 (suc m) (⟨ x) k xs = go 1 m x (k ∘ ⟨_) xs
  go 1 (suc m) (⟨ x) k xs = go 2 m x (k ∘ ⟨_) xs
  go (suc n@(suc _)) (suc m) (⟨ x) k xs = go (suc (suc n)) m x (k ∘ ⟨_) (rights (suc n) (suc m) k xs)
  go (suc n) m (⟩ x) k xs =
    let p = go n m x (k ∘ ⟩_) xs
    in pushEnd (suc n) m k (k (⟩ x)) (lefts (suc n) m k _) (pushLefts (suc n) m k (k (⟩ x)) (rights (suc n) m k xs) p)
