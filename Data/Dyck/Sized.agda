module Data.Dyck.Sized where

open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head; foldl′)

private
  variable
    n m k : ℕ

private
  variable
    n⊙ m⊙ k⊙ : ℕ → ℕ

data Stack : ℕ → ℕ → Type where
  [] : Stack 1 0
  push : Stack (1 + n) m → Stack n (1 + m)
  pull : Stack (1 + n) m → Stack (2 + n) m

data Tree : Type where
  ⟨⟩ : Tree
  _*_ : Tree → Tree → Tree

size⊙ : Tree → ℕ → ℕ
size⊙ ⟨⟩ = suc
size⊙ (xs * ys) = size⊙ xs ∘ size⊙ ys

size : Tree → ℕ
size t = size⊙ t zero

tree→stack⊙ : (t : Tree) → Stack (suc m) k → Stack m (size⊙ t k)
tree→stack⊙ ⟨⟩         = push
tree→stack⊙ (xs * ys) = tree→stack⊙ xs ∘ tree→stack⊙ ys ∘ pull

tree→stack : (t : Tree) → Stack 0 (size t)
tree→stack tr = tree→stack⊙ tr []

stack→tree⊙ : Stack n m → Vec Tree n → Tree
stack→tree⊙ []        (v ∷ [])       = v
stack→tree⊙ (push is) st             = stack→tree⊙ is (⟨⟩ ∷ st)
stack→tree⊙ (pull is) (t₁ ∷ t₂ ∷ st) = stack→tree⊙ is (t₂ * t₁ ∷ st)

stack→tree : Stack 0 n → Tree
stack→tree ds = stack→tree⊙ ds []

stack→tree-size⊙ :  {st : Vec Tree n} (is : Stack n m) →
 size (stack→tree⊙ is st) ≡ foldl′ size⊙ m st
stack→tree-size⊙  []       = refl
stack→tree-size⊙ (push is) = stack→tree-size⊙ is
stack→tree-size⊙ (pull is) = stack→tree-size⊙ is

tree→stack→tree⊙ :  {is : Stack (1 + n) m} {st : Vec Tree n} (e : Tree) →
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

open import Cubical.Foundations.Prelude using (substRefl)

stack→tree→stack⊙ :  {st : Vec Tree n} (is : Stack n m) →
 subst (Stack 0) (stack→tree-size⊙ is) (tree→stack (stack→tree⊙ is st))
   ≡
     foldlNN Stack size⊙ tree→stack⊙ is st
stack→tree→stack⊙  []       = substRefl {B = Stack 0} _
stack→tree→stack⊙ (push is) = stack→tree→stack⊙ is
stack→tree→stack⊙ (pull is) = stack→tree→stack⊙ is

STree : ℕ → Type
STree = fiber size

open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Data.Nat.Properties using (isSetℕ)

tree-stack : STree n ⇔ Stack 0 n
tree-stack .fun (t , n) = subst (Stack 0) n (tree→stack t)
tree-stack .inv st .fst = stack→tree st
tree-stack .inv st .snd = stack→tree-size⊙ st
tree-stack .leftInv  (t , sz≡) =
  Σ≡Prop
  (λ _ → isSetℕ _ _)
  (J
    (λ n sz≡ → stack→tree (subst (Stack 0) sz≡ (tree→stack t)) ≡ t)
    (cong stack→tree (substRefl {B = Stack 0} (tree→stack t)) ; tree→stack→tree⊙ t) sz≡)
tree-stack .rightInv st = stack→tree→stack⊙ st
